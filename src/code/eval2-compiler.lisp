(in-package "SB!EVAL2")

#+(or)
'(;; these can be represented as Lisp code!
  (%var-ref sym)
  (%var-set sym ...)
  (%env-ref nesting offset)
  (%env-set nesting offset ...)
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
        #+sbcl
        (when morep
          (error "The interpreter does not support the lambda-list keyword ~S"
                 'sb!int:&more))
        (let* ((keywords (mapcar #'lambda-key keys))
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
                                            ;;XXX
                                            (prepare-form default-value))
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
                        (prepare-form
                         (if namep
                             `(block ,(fun-name-block-name name) ,@body)
                             `(progn ,@body)))))
               (unbound (gensym)))
          (setq varspecs (nreverse varspecs))
          (flet
              ((handle-arguments (&rest args)
                 (declare (dynamic-extent args))
                 ;; All this ELT and LENGTH stuff is not as
                 ;; inefficient as it looks.  SBCL transforms
                 ;; &rest into &more here.
                 (dnlet iter
                     ((rest
                       (when (or restp keyp)
                         (loop for i
                               from (+ required-num optional-num)
                               below (length args)
                               collect (elt args i))))
                      (restnum (max 0 (- (length args) (+ required-num optional-num))))
                      (keys-checked-p nil)
                      (my-default-values* default-values*)
                      (my-keywords keywords)
                      (my-varspecs varspecs)
                      (argi 0)        ;how many actual arguments have
                                      ;been processed
                      (vari 0)        ;how many lexical vars have been
                                      ;bound
                      (i 0))          ;how many formal arguments have
                                      ;been processed
                     (declare (fixnum restnum argi vari i))
                     (flet ((push-args (&rest values)
                              ;; Push VALUES onto the
                              ;; environment.
                              (incf i)
                              (dolist (value values)
                                (let ((varspec (pop my-varspecs)))
                                  (if (eq varspec :lexical)
                                      (setf
                                       (environment-value *env* 0 (incff vari))
                                       value)
                                      (let ((var (cdr varspec)))
                                        (assert (eq :special
                                                    (car varspec))
                                                (varspec))
                                        (return-from iter
                                          (progv (list var) (list value)
                                            (iter rest restnum keys-checked-p
                                                  my-default-values* my-keywords
                                                  my-varspecs argi vari i)))))))))
                       (declare (inline push-args))
                       (prog ()
                        positional
                          (when (>= argi (length args))
                            (go missing-optionals))
                          (when (>= argi (the fixnum
                                              (+ required-num optional-num)))
                            (go rest))
                          (if (>= argi required-num)
                              (progn
                                (pop my-default-values*)
                                (push-args (elt args (incff argi)) t))
                              (push-args (elt args (incff argi))))
                          (go positional)
                        missing-optionals
                          (unless (>= argi required-num)
                            (error 'simple-program-error
                                   :format-control "invalid number of arguments: ~D (expected: >=~D)"
                                   :format-arguments (list (length args) required-num)))
                          (when (>= i (the fixnum (+ required-num
                                                     optional-num)))
                            (go rest))
                          (let ((val* (pop my-default-values*)))
                            (push-args (funcall (the eval-closure val*))
                                       nil))
                          (go missing-optionals)
                        rest
                          (when (>= i (the fixnum
                                           (+ (if restp 1 0)
                                              (the fixnum
                                                   (+ required-num optional-num)))))
                            (go keys))
                          (when restp
                            (push-args rest))
                        keys
                          (unless keyp
                            (unless (or restp (= argi (length args)))
                              (error 'simple-program-error
                                     :format-control "invalid number of arguments: ~D (expected: <=~D)"
                                     :format-arguments (list (length args) (+ required-num optional-num))))
                            (go aux))
                          (unless (evenp restnum)
                            (error 'simple-program-error
                                   :format-control "odd number of keyword arguments: ~S"
                                   :format-arguments (list rest)))
                          (when (>= i
                                    (the fixnum
                                         (+ (if restp 1 0)
                                            (the fixnum
                                                 (+ required-num
                                                    (the fixnum
                                                         (+ optional-num
                                                            key-num)))))))
                            (unless (or keys-checked-p
                                        allowp
                                        (getf rest :allow-other-keys nil))
                              (loop for (k) on rest by #'cddr
                                    unless (or (eq k :allow-other-keys)
                                               (member k keywords :test #'eq))
                                    do (error 'simple-program-error
                                              :format-control "unknown &KEY argument: ~A"
                                              :format-arguments (list k)))
                              (setq keys-checked-p t))
                            (go aux))
                          (let* ((key  (the symbol (pop my-keywords)))
                                 (val* (pop my-default-values*))
                                 (x    (getf rest key unbound)))
                            (if (eq unbound x)
                                (progn
                                  (push-args (funcall (the eval-closure val*))
                                             nil))
                                (progn
                                  (push-args x t))))
                          (go keys)
                        aux
                          (when (>= i
                                    (+ (if restp 1 0)
                                       (the fixnum
                                            (+ required-num
                                               (the fixnum
                                                    (+ optional-num
                                                       key-num))
                                               aux-num))))
                            (go final-call))
                          (let ((val* (pop my-default-values*)))
                            (push-args (funcall (the eval-closure val*))))
                          (go aux)
                        final-call
                          (assert (null my-default-values*)
                                  (my-default-values*))
                          (return
                            (funcall body*)))))))
              ;;(declare (inline handle-arguments))  ;crashes the compiler! lp#1203260
            (let ((current-path #+sbcl (and (boundp 'sb!c::*current-path*) sb!c::*current-path*))
                  (source-info #+sbcl (and (boundp 'sb!c::*source-info*) sb!c::*source-info*)))
              (declare (ignorable current-path source-info))
              (if envp
                  (eval-lambda ()
                    (let ((env *env*))
                      (interpreted-lambda (name current-path source-info) (&rest args)
                        (declare (dynamic-extent args))
                        (with-environment (make-environment debug-info env varnum)
                          (apply #'handle-arguments args)))))
                  (eval-lambda ()
                    (let ((env *env*))
                      (interpreted-lambda (name current-path source-info) (&rest args)
                        (declare (dynamic-extent args))
                        (with-dynamic-extent-environment (*env* debug-info env varnum)
                          (apply #'handle-arguments args)))))))))))))

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
                              (prepare-nil)))))
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
                                   (compile-form
                                    `(setf (environment-value *env* ,nesting ,offset)
                                           ,valform))))
                                (t
                                 (assume-special *context* var)
                                 (prevent-constant-modification var)
                                 (compile-form
                                  `(setf (symbol-value ',var)
                                         ,valform)))))))            
            ((flet)
             ;;??????
             )
            ((labels)
             ;;??????
             )
            ((let)
             (destructuring-bind (bindings &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (let* ((real-bindings (mapcar (lambda (form)
                                                 (if (listp form)
                                                     (cons (first form) (second form))
                                                     (cons form nil)))
                                               bindings))
                        (vars (mapcar #'car real-bindings))
                        (varnum (length vars))
                        (envp (or (> varnum +stack-max+)
                                  (maybe-closes-p *context* `(progn ,@body))))
                        (new-context
                          (context-add-env-lexicals *context* (list)))
                        (debug-info
                          (make-debug-record new-context))
                        srav-laiceps)
                   `(with-indefinite-extent-environment (*env* ,debug-info *env* ,varnum)
                      ,(nlet iter ((remaining-bindings real-bindings))
                         (if (endp remaining-bindings)
                             `(progn ,@exprs)
                             (destructuring-bind (var . value-form)
                                 (first remaining-bindings)
                               (let ((val* (compile-form
                                            `(without-environment ,value-form))))
                                 (if (or (member (the symbol var) specials)
                                         (globally-special-p var))
                                     (progn
                                       (context-add-special! new-context var)
                                       `(%with-binding ,var ,val*
                                          ,(iter (rest remaining-bindings))))
                                     (progn
                                       (context-add-env-lexical! new-context var)
                                       (let* ((lexical (context-find-lexical new-context var))
                                              (nesting (lexical-nesting lexical))
                                              (offset (lexical-offset lexical)))
                                        `(progn
                                           ,(compile-form
                                             `(setf (environment-value *env* ,nesting ,offset)
                                                    ,val*))
                                           ,(iter (rest remaining-bindings))))))))))
                      ,@(with-context new-context (mapcar #'compile-form exprs)))))))
            ((let*)
             ;;??????
             )
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
             ;;???????
             )
            ((block)
             (compile-form `(%block ,@(rest form)) mode))
            ((return-from)
             (compile-form `(%return-from ,@(rest form)) mode))
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
             (compile-form `(,(first form) ,@(mapcar #'compile-form (rest form)))))
            ((progn)
             (compile-progn (rest form) mode))
            #+(or)
            ((go)
             (compile-form `(%go ,@(rest form)) mode))
            #+(or)
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

