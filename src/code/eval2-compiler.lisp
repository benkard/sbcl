(in-package "SB!EVAL2")

#+(or)
'(;; these can be represented as Lisp code!
  (%var-ref sym)
  (%var-set sym ...)
  (%envref nesting offset)
  (%envset nesting offset ...)
  ;; these are primitives
  (%fdef-ref sym)
  (%local-call nesting offset ...)
  (%global-call sym ...)
  ;;
  (%mvb) ;--> multiple-value-list --> dolist
  ;;
  (%eval-when <times> ...)
  ;;
  (%lambda lambda-list ...)
  ;;
  ;;nil
  ;;!!punt to (setf values)!! (%mvsetq)
  ;;(%if r0 ... ...)
  ;;(%catch r0 ...)
  ;;(%block name ...)
  ;;(%load-time-value ...)
  ;;(%mvcall ...)
  ;;???(%mvprog1 ... ...)
  ;;(%quote ...)
  ;;(%progv r0 r1 ...)
  ;;(%return-from name r0)
  ;;(%throw r0 r1)
  ;;(%unwind-protect ... ...)
  ;;(%go ...)
  ;;(%tagbody ...)
  )


(defvar *context*)

(defun compile-nil ()
  nil)

(defun compile-progn (forms &optional (*mode* *mode*))
  `(progn ,@(mapcar #'compile-form forms)))

(defun compile-macro-lambda (name lambda-form)
  (destructuring-bind (lambda-list &rest body)
      lambda-form
    (let* ((whole (gensym "WHOLE"))
           (env   (gensym "ENV"))
           (body-form (parse-macrolet-binding-form lambda-list
                                                   whole
                                                   body
                                                   name
                                                   env)))
      (compile-lambda `((,whole ,env) ,body-form)
                      ;;:name name ;unnecessary because of
                                   ;PARSE-MACROLET-BINDING-FORM
                      ))))

(defun lambda-binding-vars (entry kind)
  (check-type kind (member :aux :optional :key :required))
  (ecase kind
    ((:key :optional)
     (etypecase entry
       (cons   (list (etypecase (first entry)
                       (cons   (second (first entry)))
                       (symbol (first entry)))
                     (if (cddr entry)
                         (third entry)
                         (gensym))))
       (symbol (list entry (gensym)))))
    ((:required)
     (etypecase entry
       (cons   (list (first entry)))
       (symbol entry)))
    ((:aux)
     (etypecase entry
       (cons   (list (first entry)))
       (symbol entry)))))

(defun lambda-binding-main-var (entry)
  (etypecase entry
    (cons   (etypecase (first entry)
              (cons   (second (first entry)))
              (symbol (first entry))))
    (symbol entry)))

(defun lambda-binding-suppliedp-var (entry)
  (etypecase entry
    (cons (third entry))
    (symbol nil)))

(defun lambda-simple-binding-vars (entry)
  (etypecase entry
    (cons   (list (first entry)))
    (symbol (list entry))))

(defun lambda-binding-default (entry)
  (etypecase entry
    (cons   (second entry))
    (symbol nil)))

(defun lambda-key (entry)
  (flet ((keywordify (sym)
           (intern (symbol-name sym) "KEYWORD")))
    (etypecase entry
      (cons   (etypecase (first entry)
                (cons   (first (first entry)))
                (symbol (keywordify (first entry)))))
      (symbol (keywordify entry)))))

(defun compile-lambda (lambda-form &key (name nil namep))
  ;;#+sbcl (declare (optimize debug (safety 3) (speed 0) (space 0) sb!c::store-closure-debug-pointer))
  (destructuring-bind (lambda-list &rest exprs) lambda-form
    (with-parsed-body (body specials) exprs
      (multiple-value-bind (required optional restp rest keyp keys allowp auxp aux
                            morep more-context more-count)
          (parse-lambda-list lambda-list)
        (declare (ignore more-context more-count))
        (declare (ignorable auxp morep))
        (setq rest (or rest (gensym "REST")))
        #+sbcl
        (when morep
          (error "The interpreter does not support the lambda-list keyword ~S"
                 'sb!int:&more))
        (let* ((argvars (append required
                                (mapcan (lambda (x) (lambda-binding-vars x :optional)) optional)
                                (and restp (list rest))
                                (mapcan (lambda (x) (lambda-binding-vars x :key)) keys)
                                (mapcan (lambda (x) (lambda-binding-vars x :aux)) aux)))
               (keywords (mapcar #'lambda-key keys))
               (required-num (length required))
               (optional-num (length optional))
               (key-num (length keys))
               (aux-num (length aux))
               (default-values (append (mapcar #'lambda-binding-default optional)
                                       (mapcar #'lambda-binding-default keys)
                                       (mapcar #'lambda-binding-default aux)))
               (new-context (make-lexical-context *context*))
               (varspecs (list))
               (varnum 0)
               (default-values*
                 (flet ((register-var (var)
                          (if (or (member var specials :test #'eq)
                                  (globally-special-p var))
                              (progn
                                (context-add-special! new-context var)
                                (push (cons :special var) varspecs))
                              (progn
                                (context-add-env-lexical! new-context var)
                                (push :lexical varspecs)
                                (incf (the fixnum varnum))))))
                   (mapc #'register-var required)
                   (flet ((process-bindings (bindings kind)
                            (loop for binding in bindings
                                  for default-value = (lambda-binding-default binding)
                                  for vars = (lambda-binding-vars binding kind)
                                  collect (with-context new-context
                                            (compile-form default-value))
                                  do (mapc #'register-var vars))))
                     (append (process-bindings optional :optional)
                             (progn (when restp (register-var rest)) '())
                             (process-bindings keys :key)
                             (process-bindings aux :aux)))))
               (envp (or (> varnum +stack-max+)
                         (maybe-closes-p *context* `(progn ,@body))
                         (some (lambda (x) (maybe-closes-p *context* x))
                               default-values)))
               (body-context (context-add-specials new-context specials))
               (debug-info (make-debug-record body-context lambda-list name))
               (body* (with-context body-context
                        (compile-form
                         (if namep
                             `(block ,(fun-name-block-name name) ,@body)
                             `(progn ,@body)))))
               (unbound (gensym)))
          (setq varspecs (nreverse varspecs))
          (let ((current-path #+sbcl (and (boundp 'sb!c::*current-path*) sb!c::*current-path*))
                (source-info #+sbcl (and (boundp 'sb!c::*source-info*) sb!c::*source-info*))
                (i 0))
            (declare (ignorable current-path source-info))
            `(%lambda (,name ,current-path ,source-info)
               (when (< %argnum ,required-num)
                 (error 'simple-program-error
                        :format-control "invalid number of arguments: ~D (expected: >=~D)"
                        :format-arguments (list (length args) required-num)))
               ,@(unless (or keyp restp)
                   `((when (> %argnum ,(+ required-num optional-num))
                       (error 'simple-program-error
                              :format-control "invalid number of arguments: ~D (expected: >=~D)"
                              :format-arguments (list (length args) required-num)))))
               ,(compile-form
                 `(let* (,@(loop for arg in required
                                 collect `(,arg (%getarg ,i))
                                 do (incf i))
                         ,@(loop for arg in optional
                                 for var = (lambda-binding-main-var arg)
                                 for default = (lambda-binding-default arg)
                                 for suppliedp = (lambda-binding-suppliedp-var arg)
                                 collect `(,var (if (< ,i %argnum)
                                                    (%getarg ,i)
                                                    ,default))
                                 when suppliedp
                                   collect `(,suppliedp (< ,i %argnum))
                                 do (incf i))
                         ,@(when (or restp keyp)
                             `((,rest (%arglistfrom ,i))))
                         ,@(loop for arg in keys
                                 for var = (lambda-binding-main-var arg)
                                 for key = (lambda-key arg)
                                 for default = (lambda-binding-default arg)
                                 for suppliedp = (lambda-binding-suppliedp-var arg)
                                 collect `(,var (getf ,rest ',key ,default))
                                 when suppliedp
                                   collect `(,suppliedp
                                             (and (get-properties ,rest '(,key)) t))
                                 do (incf i))
                         ,@(loop for arg in aux
                                 for var = (lambda-binding-main-var arg)
                                 for default = (lambda-binding-default arg)
                                 collect `(,var ,default)))
                    (declare (special ,@specials))
                    ,@(when (and keyp (not allowp))
                        `((unless (getf ,rest :allow-other-keys nil)
                            (let ((to-check ,rest))
                              (unless (endp to-check)
                                (let ((k (pop to-check)))
                                  (unless (member k ',(cons :allow-other-keys (mapcar #'lambda-key keys)))
                                    (error 'simple-program-error
                                           :format-control "unknown &KEY argument: ~A"
                                           :format-arguments (list k))))
                                (pop to-check))))))
                    ,@body)))))))))

(defun compile-ref (var)
  (if (context-var-lexical-p *context* var)
      (let* ((lexical (context-find-lexical *context* var))
             (nesting (lexical-nesting lexical))
             (offset (lexical-offset lexical)))
        `(%envref ,nesting ,offset))
      (if (globally-constant-p var)
          (eval-lambda (env)
            (declare (ignore env))
            `(symbol-value ',var))
          (progn
            (assume-special *context* var)
            (eval-lambda (env)
              (declare (ignore env))
              (unless (boundp var)
                (error 'unbound-variable :name var))
              `(symbol-value ',var))))))

(defun compile-function-ref (function-name)
  (compile-ref `(function ,function-name)))

(defun compile-local-call (f args)
  (let* ((lexical (context-find-lexical *context* `(function ,f)))
         (nesting (lexical-nesting lexical))
         (offset (lexical-offset lexical)))
    `(%local-call ,nesting ,offset ,@(mapcar #'compile-form args))))

(defun compile-global-call (f args)
  (let ((args* (mapcar #'compile-form args)))
    `(%global-call ,f ,@args*)))

(defun compile-form (form
                     &optional (mode      *mode*)
                               (*context* *context*)
                     &aux      (*mode*    :execute)
                               #+sbcl
                               (sb!c::*current-path*
                                (when (and (boundp 'sb!c::*source-paths*)
                                           (or (sb!c::get-source-path form)
                                               (boundp 'sb!c::*current-path*))
                                           (sb!c::source-form-has-path-p form))
                                  (sb!c::ensure-source-path form))))
  (values
   (cond
     ((self-evaluating-p form)
      ;;FIXME load forms?
      form)
     (t
      (etypecase form
        (symbol
         (let ((macro? (context-find-symbol-macro *context* form)))
           (if macro?
               (compile-form macro?)
               (compile-ref form))))
        (cons
         (case (first form)
           ((if)
            (destructuring-bind (a b &optional c) (rest form)
              (let ((a* (compile-form a))
                    (b* (compile-form b))
                    (c* (compile-form c)))
                `(if ,a* ,b* ,c*))))
           ((function)
            (let ((fun-form (second form)))
              (etypecase fun-form
                (symbol
                 (compile-function-ref fun-form))
                (cons
                 (case (first fun-form)
                   ((lambda)
                    (compile-lambda (rest fun-form)))
                   #+sbcl
                   ((sb!int:named-lambda)
                    (compile-lambda (cddr fun-form) :name (cadr fun-form)))
                   (t
                    #+sbcl (assert (sb!int:valid-function-name-p fun-form))
                    #+ccl  (assert (ccl::valid-function-name-p fun-form))
                    (compile-function-ref fun-form)))))))
           ((lambda)
            (compile-lambda (rest form)))
           ((declare)
            (warn "DECLARE in form context.")
            (compile-nil))
           ((eval-when)
            (destructuring-bind ((&rest times) &body body) (rest form)
              (cond ((member mode '(:not-compile-time :compile-time-too))
                     (let ((ct (or (member :compile-toplevel times)
                                   (member 'cl:compile times)))
                           (lt (or (member :load-toplevel times)
                                   (member 'cl:load times)))
                           (e  (or (member :execute times)
                                   (member 'cl:eval times))))
                       (cond ((and lt ct)
                              (compile-progn body :compile-time-too))
                             ((and lt e)
                              (compile-progn body mode))
                             (lt
                              (compile-progn body :not-compile-time))
                             (ct
                              (compile-progn body))
                             ((and e (eq mode :compile-time-too))
                              (compile-progn body))
                             (t
                              (compile-nil)))))
                    ((or (member :execute times)
                         (member 'cl:eval times))
                     (compile-progn body))
                    (t
                     (compile-nil)))))
           ((setq)
            `(progn
               ,@(loop for (var valform) on (rest form) by #'cddr
                       collect
                          (cond ((context-var-symbol-macro-p *context* var)
                                 (let ((form (context-find-symbol-macro *context* var)))
                                   (compile-form `(setf ,form ,valform))))
                                ((context-var-lexical-p *context* var)
                                 (let* ((lexical (context-find-lexical *context* var))
                                        (nesting (lexical-nesting lexical))
                                        (offset  (lexical-offset lexical)))
                                   `(%envset ,nesting ,offset ,valform)))
                                (t
                                 (assume-special *context* var)
                                 (prevent-constant-modification var)
                                 (compile-form
                                  `(setf (symbol-value ',var)
                                         ,valform)))))))            
            ((flet labels)
             (destructuring-bind (bindings &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (declare (ignore specials))
                 (let* ((function-names (mapcar #'first bindings))
                        (body-context (context-add-env-lexicals
                                       *context*
                                       (mapcar #'(lambda (name)
                                                   `(function ,name))
                                               function-names)))
                        (binding-context
                          (if (eq 'flet (first form))
                              (context-add-env-lexicals *context* '())
                              body-context))
                        (debug-info
                          (make-debug-record body-context))
                        (varnum
                          (length bindings)))
                  `(with-indefinite-extent-environment (*env* ,debug-info *env* ,varnum)
                     ,@(loop for (name lambda-list . body) in bindings
                             for i from 0
                             collect
                                `(%envset 0 ,i
                                          ,(with-context binding-context
                                             (compile-lambda (cons lambda-list body)
                                                             :name name))))
                     ,@(with-context body-context
                         (mapcar #'compile-form body)))))))
            ((let let*)
             (destructuring-bind (bindings &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (let* ((real-bindings (mapcar (lambda (form)
                                                 (if (listp form)
                                                     (cons (first form) (second form))
                                                     (cons form nil)))
                                               bindings))
                        (vars (mapcar #'car real-bindings))
                        (varnum (length vars))
                        #+(or)
                        (envp (or (> varnum +stack-max+)
                                  (maybe-closes-p *context* `(progn ,@body))))
                        (binding-context
                          (context-add-env-lexicals *context* (list)))
                        (body-context
                          (if (eq (first form) 'let)
                              (context-add-env-lexicals *context* (list))
                              binding-context))
                        (debug-info
                          (make-debug-record body-context)))
                   (with-context binding-context
                     `(with-indefinite-extent-environment (*env* ,debug-info *env* ,varnum)
                        ,(let ((dynvals-sym (gensym "DYNVALS"))
                               (dynvars-sym (gensym "DYNVARS")))
                           `(,@(if (eq (first form) 'let)
                                   `(progv (,dynvars-sym ,dynvals-sym) ())
                                   `(progn))
                              ,@(nlet iter ((remaining-bindings real-bindings))
                                 (if (endp remaining-bindings)
                                     (if (eq (first form) 'let)
                                         `((progv ,dynvars-sym ,dynvals-sym
                                             ,@(with-context body-context
                                                 (mapcar #'compile-form body))))
                                         `(,@(with-context body-context
                                               (mapcar #'compile-form body))))
                                     (destructuring-bind (var . value-form)
                                         (first remaining-bindings)
                                       (let ((val* (with-context binding-context
                                                     (compile-form value-form))))
                                         (if (or (member (the symbol var) specials)
                                                 (globally-special-p var))
                                             (progn
                                               (context-add-special! body-context var)
                                               (if (eq (first form) 'let)
                                                   `((%varpush ,val* ,dynvals-sym)
                                                     (%varpush ',var ,dynvars-sym)
                                                     ,@(iter (rest remaining-bindings)))
                                                   `((%with-binding ,var ,val*
                                                       ,@(iter (rest remaining-bindings))))))
                                             (progn
                                               (context-add-env-lexical! body-context var)
                                               (let* ((lexical (context-find-lexical body-context var))
                                                      (nesting (lexical-nesting lexical))
                                                      (offset (lexical-offset lexical)))
                                                 `((%envset ,nesting ,offset ,val*)
                                                   ,@(iter (rest remaining-bindings))))))))))))))))))
            ((load-time-value)
             ;;??????
             )
            ((locally)
             (destructuring-bind (&rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (with-context (context-add-specials *context* specials)
                   (compile-progn body)))))
            ((multiple-value-setq)
             (destructuring-bind (vars values-form) (rest form)
               (if vars
                   (compile-form `(values (setf (values ,@vars) ,values-form)))
                   (compile-form `(values ,values-form)))))
            ((multiple-value-bind)
             (destructuring-bind (vars form &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (compile-form
                  `(let ,vars
                     (declare (special ,@specials))
                     (setf (values ,vars) ,form)
                     ,@body)))))
            ((quote)
             form)
            #+sbcl
            ((sb!ext:truly-the)
             `(sb!ext:truly-the ,@(mapcar #'compile-form (rest form))))
            #+sbcl
            ((sb!int:named-lambda)
             )
            #+ccl
            ((ccl:nfunction)
             )
            ((symbol-macrolet)
             (destructuring-bind (bindings &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (let ((bindings (mapcar (lambda (form)
                                           (destructuring-bind (var macro-form) form
                                             (when (or (globally-special-p var)
                                                       (member var specials))
                                               (error 'simple-program-error
                                                      :format-control "Attempt to bind a special variable with SYMBOL-MACROLET: ~S"
                                                      :format-arguments (list var)))
                                             (when (constantp var)
                                               (error 'simple-program-error
                                                      :format-control "Attempt to bind a special variable with SYMBOL-MACROLET: ~S"
                                                      :format-arguments (list var)))
                                             (cons var macro-form)))
                                         bindings)))
                   (with-context (context-add-specials
                                  (context-add-symbol-macros *context* bindings)
                                  specials)
                     (compile-progn body mode))))))
            ((macrolet)
             (destructuring-bind (bindings &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (let ((bindings (mapcar (lambda (form)
                                           (cons (first form)
                                                 (with-environment (make-null-environment)
                                                   (funcall
                                                    (prepare-form
                                                     (compile-macro-lambda (first form)
                                                                           (rest form)))))))
                                         bindings)))
                   (with-context (context-add-specials
                                  (context-add-macros *context* bindings)
                                  specials)
                     (compile-progn body mode))))))
            ((catch unwind-protect multiple-value-call multiple-value-prog1 progv
              the throw)
             `(,(first form) ,@(mapcar #'compile-form (rest form))))
            ((progn)
             (compile-progn (rest form) mode))
            ((block)
             (compile-form `(%block ,@(rest form)) mode))
            ((return-from)
             (compile-form `(%return-from ,@(rest form)) mode))
            ((go)
             (compile-form `(%go ,@(rest form)) mode))
            ((tagbody)
             (compile-form `(%tagbody ,@(rest form)) mode))
            (otherwise
             ;; FIXME: Handle SETF expanders?
             (destructuring-bind (f . args) form
               (check-type f (or list symbol))
               (let ((local-macro? (context-find-macro *context* f))
                     (global-macro? (and (symbolp f) (macro-function f))))
                 (cond
                   (local-macro?
                    (let ((macro-function local-macro?))
                      (compile-form (funcall (the function macro-function)
                                             form
                                             (context->native-environment *context*))
                                    mode)))
                   ((local-function-p *context* f)
                    (compile-local-call f args))
                   (global-macro?
                    (compile-form
                     (funcall global-macro? form (context->native-environment *context*))
                     mode))
                   ((and (listp f)
                         (eq 'lambda (first f)))
                    ;;transform into funcall
                    (compile-form
                     `(funcall #',f ,@args)
                     mode))
                   (t
                    (compile-global-call f args)))))))))))))

