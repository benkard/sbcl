(in-package #+sbcl "SB!EVAL2" #-sbcl "SB-EVAL2")

#+sbcl
(declaim (optimize (debug 2) (space 2) (speed 2) (safety 0) (compilation-speed 0)
                   (sb!c::store-closure-debug-pointer 3)))

(defvar *mode* :not-compile-time)
(defvar *form*)
(defvar *env*)

(declaim (inline call-with-environment))
(defun call-with-environment (env thunk)
  (let ((*env* env))
    (funcall thunk)))

(defun maybe-closes-p (context form)
  "Check whether FORM potentially closes over anything not bound in CONTEXT.

We use this to determine whether environments corresponding to
children of CONTEXT can be stack-allocated."
  (declare (ignore context form))
  ;; FIXME
  ;;
  ;; What we really want to do here is macroexpand FORM and have a
  ;; look at whether there are any potential closures there.  It
  ;; should be pretty easy to simply check for the mere presence of
  ;; LAMBDA, SB-INT:NAMED-LAMBDA, FLET, and LABELS.
  ;;
  ;; Beyond that, it's tricky.  We mustn't assume that FORM doesn't
  ;; close over the new enviroment we want to establish just because
  ;; it doesn't close over one of the new environment's direct lexical
  ;; variables.  There could be a child environment it closes over,
  ;; which still means we need to keep the environment on the heap.
  t)

(defun parse-tagbody-tags-and-bodies (forms)
  (let ((next-form (gensym))
        (finishp nil))
    (loop until finishp
          collect
             (progn
               (unless forms
                 (setq finishp (null forms)))
               (let ((tag next-form)
                     (current-forms (loop for current-form = (pop forms)
                                          do (setq next-form current-form)
                                          until (atom current-form)
                                          collect current-form)))
                 (cons tag current-forms))))))

(declaim (ftype (function (symbol context) eval-closure) prepare-ref))
(defun prepare-ref (var context)
  (if (context-var-lexical-p context var)
      (let* ((lexical (context-find-lexical context var))
             (nesting (lexical-nesting lexical))
             (offset (lexical-offset lexical)))
        (eval-lambda ()
          (environment-value *env* nesting offset)))
      (if (globally-constant-p var)
          (eval-lambda ()
            (symbol-value var))
          (progn
            (assume-special context var)
            (eval-lambda ()
              (unless (boundp var)
                (error 'unbound-variable :name var))
              (symbol-value var))))))


(defun body-decls&forms (exprs)
  (let* ((decl-exprs
           (loop while (and (consp (first exprs))
                            (eq 'declare (first (first exprs))))
                 for expr = (pop exprs)
                 collect expr))
         (decls (reduce #'append (mapcar #'rest decl-exprs))))
    (values decls exprs)))

(defun decl-specials (declaration)
  (when (eq (first declaration) 'special)
    (rest declaration)))


(declaim (ftype (function ((or symbol list) context) eval-closure) prepare-function-ref))
(defun prepare-function-ref (function-name context)
  (if (context-var-lexical-p context `(function ,function-name))
      (let* ((lexical (context-find-lexical context `(function ,function-name)))
             (nesting (lexical-nesting lexical))
             (offset  (lexical-offset lexical)))
        (eval-lambda ()
          (environment-value *env* nesting offset)))
      #+sbcl
      (let ((f* (sb!c::fdefinition-object function-name t)))
        (eval-lambda ()
          (or (sb!c::fdefn-fun f*)
              (error 'undefined-function :name function-name))))
      #-sbcl
      (eval-lambda ()
        (fdefinition function-name))))

(declaim (ftype (function () eval-closure) prepare-nil))
(defun prepare-nil ()
  (eval-lambda () nil))

(declaim (ftype (function ((or symbol list) list context) eval-closure) prepare-local-call))
(defun prepare-local-call (f args context)
  (let* ((args* (mapcar (lambda (form) (prepare-form form context)) args))
         (flex (context-find-function context f))
         (offset (lexical-offset flex))
         (nesting (lexical-nesting flex)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          (let ((argvars (loop for i from 0 below m%
                               collect (gensym (format nil "ARG~D-" i)))))
            `(let ,(loop for var in argvars
                         for i from 0 below m%
                         collect `(,var (nth ,i args*)))
               (eval-lambda ()
                 (funcall (the function (environment-value *env* nesting offset))
                          ,@(loop for var in argvars
                                  collect `(funcall (the eval-closure ,var))))))))
        (eval-lambda ()
          (apply (the function (environment-value *env* nesting offset))
                 (mapcar (lambda (x) (funcall (the eval-closure x))) args*))))))

(declaim (ftype (function ((or symbol list) list context) eval-closure) prepare-global-call))
(defun prepare-global-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args))
        #+sbcl
        (f* (sb!c::fdefinition-object f t)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          (let ((argvars (loop for i from 0 below m%
                               collect (gensym (format nil "ARG~D-" i)))))
            `(let ,(loop for var in argvars
                         for i from 0 below m%
                         collect `(,var (nth ,i args*)))
               (eval-lambda ()
                 (funcall #+sbcl (or (sb!c::fdefn-fun f*)
                                     (error 'undefined-function :name f))
                          #-sbcl f
                          ,@(loop for var in argvars
                                  collect `(funcall (the eval-closure ,var))))))))
        (eval-lambda ()
          (apply #+sbcl (or (sb!c::fdefn-fun f*)
                            (error 'undefined-function :name f))
                 #-sbcl f
                 (mapcar (lambda (x) (funcall (the eval-closure x)))
                         args*))))))

(declaim (ftype (function (eval-closure list context) eval-closure) prepare-direct-call))
(defun prepare-direct-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args)))
    (eval-lambda ()
      (apply (the (or symbol function) (funcall (the eval-closure f)))
             (mapcar (lambda (x) (funcall (the eval-closure x))) args*)))))

(declaim (ftype (function (list context &optional symbol)
                          (values eval-closure &rest nil))
                prepare-progn))
(defun prepare-progn (forms context &optional (*mode* *mode*))
  (let ((body* (mapcar (lambda (form) (prepare-form form context)) forms)))
    (if (null body*)
        (prepare-nil)
        (let ((forms* (butlast body*))
              (last-form* (first (last body*))))
          (eval-lambda ()
            (dolist (form* forms*)
              (funcall (the eval-closure form*)))
            (funcall (the eval-closure last-form*)))))))

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

(declaim (ftype (function * eval-closure) prepare-macro-lambda))
(defun prepare-macro-lambda (name lambda-form context)
  (destructuring-bind (lambda-list &rest body)
      lambda-form
    (let* ((whole (gensym "WHOLE"))
           (env   (gensym "ENV"))
           (body-form (parse-macrolet-binding-form lambda-list
                                                   whole
                                                   body
                                                   name
                                                   env)))
      (prepare-lambda `((,whole ,env) ,body-form)
                      context
                      ;;:name name ;unnecessary because of
                                   ;PARSE-MACROLET-BINDING-FORM
                      ))))

(declaim (ftype (function * eval-closure) prepare-lambda))
(defun prepare-lambda (lambda-form context &key (name nil namep))
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
               (new-context (make-lexical-context context))
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
                                  collect (prepare-form default-value new-context)
                                  do (mapc #'register-var vars))))
                     (append (process-bindings optional :optional)
                             (progn (when restp (register-var rest)) '())
                             (process-bindings keys :key)
                             (process-bindings aux :aux)))))
               (envp (or (> varnum +stack-max+)
                         (maybe-closes-p context `(progn ,@body))
                         (some (lambda (x) (maybe-closes-p context x))
                               default-values)))
               (body-context (context-add-specials new-context specials))
               (debug-info (make-debug-record body-context lambda-list name))
               (body* (prepare-form
                       (if namep
                           `(block ,(fun-name-block-name name) ,@body)
                           `(progn ,@body))
                       body-context))
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

(defun assume-special (context var)
  (unless (or (globally-special-p var)
              (context-var-special-p context var))
    (warn 'simple-warning
          :format-control "Undefined variable: ~S"
          :format-arguments (list var))))

(defun prevent-constant-modification (var)
  (when (globally-constant-p var)
    (warn "~S is a constant and thus can't be set." var)))

(declaim (ftype (function (* context &optional symbol) eval-closure) prepare-form))
(defun prepare-form (form context &optional (mode *mode*)
                                  &aux (*mode* :execute)
                                       (*form* form)
                                       #+sbcl
                                       (sb!c::*current-path*
                                        (when (and (boundp 'sb!c::*source-paths*)
                                                   (or (sb!c::get-source-path form)
                                                       (boundp 'sb!c::*current-path*))
                                                   (sb!c::source-form-has-path-p form))
                                          (sb!c::ensure-source-path form))))
  ;;(declare (optimize speed (safety 0) (space 1) (debug 0)))
  (values
   (cond
     ((self-evaluating-p form)
      (eval-lambda () form))
     (t
      (etypecase form
        (symbol
         (let ((macro? (context-find-symbol-macro context form)))
           (if macro?
               (prepare-form macro? context mode)
               (prepare-ref form context))))
        (cons
         (case (first form)
           ((if)
            (destructuring-bind (a b &optional c) (rest form)
              (let ((a* (prepare-form a context))
                    (b* (prepare-form b context))
                    (c* (prepare-form c context)))
                (eval-lambda () (if (funcall a*) (funcall b*) (funcall c*))))))
           ((function)
            (let ((fun-form (second form)))
              (etypecase fun-form
                (symbol
                 (prepare-function-ref fun-form context))
                (cons
                 (case (first fun-form)
                   ((lambda)
                    (prepare-lambda (rest fun-form) context))
                   #+sbcl
                   ((sb!int:named-lambda)
                    (prepare-lambda (cddr fun-form) context :name (cadr fun-form)))
                   (t
                    #+sbcl (assert (sb!int:valid-function-name-p fun-form))
                    #+ccl  (assert (ccl::valid-function-name-p fun-form))
                    (prepare-function-ref fun-form context)))))))
           ((lambda)
            (prepare-lambda (rest form) context))
           ((setq)
            (let ((binding-forms (rest form)))
              (let ((bindings
                      (loop for (var valform) on binding-forms by #'cddr
                            collect var
                            collect
                               (cond ((context-var-symbol-macro-p context var)
                                      (let ((form
                                              (context-find-symbol-macro context var)))
                                        (prepare-form `(setf ,form ,valform)
                                                      context)))
                                     ((context-var-lexical-p context var)
                                      (context-find-lexical context var))
                                     (t
                                      (assume-special context var)
                                      (prevent-constant-modification var)
                                      :special))
                            collect (prepare-form valform context))))
                (eval-lambda ()
                  (loop for (var info val*) on bindings by #'cdddr
                        for value = (funcall (the eval-closure val*))
                        for result =
                           (etypecase info
                             (function ;symbol macro setter
                              (funcall info))
                             (lexical
                              (setf (environment-value *env*
                                                       (lexical-nesting info)
                                                       (lexical-offset info))
                                    value))
                             (keyword
                              (setf (symbol-value var) value)))
                        finally (return result))))))
           ((catch)
            (destructuring-bind (tag &body body) (rest form)
              (let ((tag* (prepare-form tag context))
                    (body* (prepare-progn body context)))
                (eval-lambda ()
                  (catch (funcall tag*)
                    (funcall body*))))))
           ((block)
            (destructuring-bind (name &body body) (rest form)
              (let* ((tag (gensym (concatenate 'string "BLOCK-" (symbol-name name))))
                     (body* (prepare-progn body (context-add-block-tag context name tag))))
                (eval-lambda ()
                  (catch tag
                    (funcall body*))))))
           ((declare)
            (warn "DECLARE in form context.")
            (prepare-nil))
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
                              (prepare-progn body context :compile-time-too))
                             ((and lt e)
                              (prepare-progn body context mode))
                             (lt
                              (prepare-progn body context :not-compile-time))
                             (ct
                              (prepare-progn body context))
                             ((and e (eq mode :compile-time-too))
                              (prepare-progn body context))
                             (t
                              (prepare-nil)))))
                    ((or (member :execute times)
                         (member 'cl:eval times))
                     (prepare-progn body context))
                    (t
                     (prepare-nil)))))
           ((flet)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((bindings* (mapcar (lambda (form)
                                            (if (listp form)
                                                (cons (first form)
                                                      (prepare-lambda (rest form)
                                                                      context
                                                                      :name (first form)))
                                                (cons form (prepare-nil))))
                                          bindings))
                       (new-context
                         (context-add-env-functions context (mapcar #'first bindings*)))
                       (debug-info
                         (make-debug-record new-context))
                       (functions (mapcar #'cdr bindings*))
                       (n (length functions))
                       (body* (prepare-progn body
                                             (context-add-specials new-context
                                                                   specials))))
                  (eval-lambda ()
                    (let ((new-env (make-environment debug-info *env* n)))
                      (loop for i from 0 to n
                            for f in functions
                            do (setf (environment-value new-env 0 i)
                                     (funcall (the eval-closure f))))
                      (with-environment new-env
                        (funcall body*))))))))
           ((labels)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((new-context (context-add-env-functions context (mapcar #'first bindings)))
                       (debug-info
                         (make-debug-record new-context))
                       (bindings* (mapcar (lambda (form)
                                            (if (listp form)
                                                (cons (first form)
                                                      (prepare-lambda (rest form) new-context :name (first form)))
                                                (cons form (prepare-nil))))
                                          bindings))
                       (functions (mapcar #'cdr bindings*))
                       (n (length functions))
                       (body* (prepare-progn body (context-add-specials new-context
                                                                        specials))))
                  (eval-lambda ()
                    (with-environment (make-environment debug-info *env* n)
                      (loop for i from 0 to n
                            for f in functions
                            do (setf (environment-value *env* 0 i)
                                     (funcall (the eval-closure f))))
                      (funcall body*)))))))
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
                                 (maybe-closes-p context `(progn ,@body))))
                       (new-context
                         (context-add-env-lexicals context (list)))
                       (debug-info
                         (make-debug-record new-context))
                       srav-laiceps)
                  (let* ((values*
                           (loop for (var . value-form) in real-bindings
                                 for val* = (prepare-form value-form context)
                                 if (or (member (the symbol var) specials)
                                        (globally-special-p var))
                                 collect (cons t   val*)
                                 and do (push var srav-laiceps)
                                        (context-add-special! new-context var)
                                 else
                                 collect (cons nil val*)
                                 and do (context-add-env-lexical! new-context var)))
                         (body* (prepare-progn body
                                               (context-add-specials
                                                new-context
                                                specials))))
                    (if envp
                        (eval-lambda ()
                          (let ((new-env (make-environment debug-info *env* varnum))
                                (slav-laiceps (list)))
                            (loop with i fixnum = 0
                                  for (specialp . val*) in values*
                                  when specialp
                                  do (push (funcall (the eval-closure val*))
                                           slav-laiceps)
                                  else
                                  do (setf (environment-value new-env 0 i)
                                           (funcall (the eval-closure val*)))
                                     (incf i))
                            (with-environment new-env
                              (progv
                                  srav-laiceps
                                  slav-laiceps
                                (funcall body*)))))
                        (eval-lambda ()
                          (with-dynamic-extent-environment (new-env debug-info *env* varnum)
                            (let ((slav-laiceps (list)))
                              (loop with i fixnum = 0
                                    for (specialp . val*) in values*
                                    when specialp
                                    do (push (funcall (the eval-closure val*))
                                             slav-laiceps)
                                    else
                                    do (setf (environment-value new-env 0 i)
                                             (funcall (the eval-closure val*)))
                                       (incf i))
                              (with-environment new-env
                                (progv
                                    srav-laiceps
                                    slav-laiceps
                                  (funcall body*))))))))))))
           ((let*)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (labels ((build-nested-let (bindings)
                           (if (null bindings)
                               `(progn ,@body)
                               (let* ((binding-form (first bindings))
                                      (var (if (listp binding-form) (first binding-form) binding-form))
                                      (val (if (listp binding-form) (second binding-form) nil)))
                                 `(let ((,var ,val))
                                    (declare (special
                                              ,@(if (or (member var specials)
                                                        (globally-special-p var))
                                                    (list var)
                                                    nil)))
                                    ,(build-nested-let (rest bindings)))))))
                  (prepare-form (build-nested-let bindings) context)))))
           ((load-time-value)
            (let ((load-form (cadr form)))
              ;; FIXME
              (prepare-form load-form context)))
           ((locally)
            (destructuring-bind (&rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let ((new-context (context-add-specials context specials)))
                  (prepare-progn body new-context)))))
           ((multiple-value-call)
            (destructuring-bind (f &rest argforms) (rest form)
              (let ((f* (prepare-form f context))
                    (argforms* (mapcar (lambda (x) (prepare-form x context)) argforms)))
                (eval-lambda ()
                  (apply (funcall (the eval-closure f*))
                         (mapcan (lambda (arg)
                                   (multiple-value-list
                                    (funcall (the eval-closure arg))))
                                 argforms*))))))
           ((multiple-value-prog1)
            (destructuring-bind (values-form &body body) (rest form)
              (let ((values-form* (prepare-form values-form context))
                    (body*        (prepare-progn body context)))
                (eval-lambda ()
                  (multiple-value-prog1
                      (funcall values-form*)
                    (funcall body*))))))
           ((multiple-value-setq)
            (destructuring-bind (vars values-form) (rest form)
              (if vars
                  (prepare-form `(values (setf (values ,@vars) ,values-form)) context)
                  (prepare-form `(values ,values-form) context))))
           ((multiple-value-bind)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (vars value-form &body exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((value-form*  (prepare-form value-form context))
                       (varspecs     (loop for var in vars
                                           collect (if (or (member var specials)
                                                           (globally-special-p var))
                                                       (cons :special var)
                                                       :lexical)))
                       (lexicals     (loop for var in vars
                                           for spec in varspecs
                                           when (eq spec :lexical)
                                           collect var))
                       (our-specials (loop for var in vars
                                           for spec in varspecs
                                           unless (eq spec :lexical)
                                           collect var))
                       (nlexicals    (list-length lexicals))
                       (new-context  (context-add-specials
                                      (context-add-env-lexicals context lexicals)
                                      specials))
                       (debug-info   (make-debug-record new-context))
                       (body*        (prepare-progn body new-context)))
                  (eval-lambda ()
                    (let* ((new-env (make-environment debug-info *env* nlexicals))
                           (values  (multiple-value-list (funcall value-form*))))
                      (progv our-specials '()
                        (loop with i = 0
                              for spec in varspecs
                              when (eq spec :lexical)
                                do (setf (environment-value new-env 0 i) (pop values))
                                   (incf i)
                              else
                                do (setf (symbol-value (cdr spec)) (pop values)))
                        (with-environment new-env
                          (funcall body*)))))))))
           ((progn)
            (prepare-progn (rest form) context mode))
           ((progv)
            (destructuring-bind (vals vars &body body) (rest form)
              (let ((vals* (prepare-form vals context))
                    (vars* (prepare-form vars context))
                    (body* (prepare-progn body context)))
                (eval-lambda ()
                  (progv (funcall vals*) (funcall vars*)
                    (funcall body*))))))
           ((quote)
            (let ((quoted-object (cadr form)))
              (eval-lambda ()
                quoted-object)))
           ((return-from)
            (destructuring-bind (name &optional value) (rest form)
              (let ((value* (prepare-form value context))
                    (tag    (context-block-tag context name)))
                (eval-lambda ()
                  (throw tag (funcall value*))))))
           ((the)
            (prepare-form (third form) context))
           ((throw)
            (destructuring-bind (tag result) (rest form)
              (let ((tag*    (prepare-form tag    context))
                    (result* (prepare-form result context)))
                (eval-lambda ()
                  (throw (funcall tag*) (funcall result*))))))
           ((unwind-protect)
            (destructuring-bind (protected &body body) (rest form)
              (let ((protected* (prepare-form  protected context))
                    (body*      (prepare-progn body      context)))
                (eval-lambda ()
                  (unwind-protect (funcall protected*)
                    (funcall body*))))))
           #+sbcl
           ((sb!ext:truly-the)
            (prepare-form (third form) context))
           #+sbcl
           ((sb!int:named-lambda)
            (prepare-lambda (cddr form) context :name (cadr form)))
           #+ccl
           ((ccl:nfunction)
            (prepare-lambda (cdaddr form) context :name (cadr form)))
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
                  (prepare-progn body
                                 (context-add-specials
                                  (context-add-symbol-macros context bindings)
                                  specials)
                                 mode)))))
           ((macrolet)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let ((bindings (mapcar (lambda (form)
                                          (cons (first form)
                                                (with-environment (make-null-environment)
                                                  (funcall
                                                   (prepare-macro-lambda (first form)
                                                                         (rest form)
                                                                         context)))))
                                        bindings)))
                  (prepare-progn body
                                 (context-add-specials
                                  (context-add-macros context bindings)
                                  specials)
                                 mode)))))
           ((go)
            (let* ((go-tag    (second form))
                   (catch-tag (context-find-go-tag context go-tag)))
              (eval-lambda ()
                (throw catch-tag go-tag))))
           ((tagbody)
            ;; 1. set up catch handler
            ;; 2. save go-tag -> tagbody-catch-tag mapping
            (let* ((jump (gensym "JUMP"))
                   (tags-and-bodies (parse-tagbody-tags-and-bodies (rest form)))
                   (new-context (context-add-go-tags context (mapcar #'car tags-and-bodies) jump))
                   (tags-and-bodies* (mapcar (lambda (x)
                                               (destructuring-bind (tag . body) x
                                                 (cons tag (prepare-progn body new-context))))
                                             tags-and-bodies)))
              (eval-lambda ()
                (block tagbody-loop
                  (let ((code tags-and-bodies*))
                    (loop
                      (setq code
                            (member (catch jump
                                      (dolist (tag-and-body* code)
                                        (funcall (the eval-closure (cdr tag-and-body*))))
                                      (return-from tagbody-loop))
                                    tags-and-bodies*
                                    :key #'car))
                      (unless code
                        (return-from tagbody-loop)))))
                nil)))
           (otherwise
            ;; FIXME: Handle SETF expanders?
            (destructuring-bind (f . args) form
              (check-type f (or list symbol))
              (let ((local-macro? (context-find-macro context f))
                    (global-macro? (and (symbolp f) (macro-function f))))
                (cond
                  (local-macro?
                   (let ((macro-function local-macro?))
                     (prepare-form (funcall (the function macro-function)
                                            form
                                            (context->native-environment context))
                                   context)))
                  ((local-function-p context f)
                   (prepare-local-call f args context))
                  (global-macro?
                   (prepare-form (funcall global-macro? form (context->native-environment context)) context))
                  ((and (listp f)
                        (eq 'lambda (first f)))
                   (let ((lambda-fn (prepare-lambda (rest f) context)))
                     (prepare-direct-call lambda-fn args context)))
                  (t
                   (prepare-global-call f args context)))))))))))
   t))

#+(or)
(defun eval (form &optional (env (make-null-environment)))
  (with-environment (env)
    (funcall (prepare-form form (make-null-context) :execute))))

#+(or)
(defun eval-tlf (form &optional (env (make-null-environment)))
  (with-environment env
    (funcall (prepare-form form (make-null-context) :not-compile-time))))


#+(or)
(defun load (filename)
  ;;FIXME: set :LOAD-TOPLEVEL time.
  (let ((eof (gensym)))
    (with-open-file (in filename)
      (loop for form = (read in nil eof nil)
            until (eq form eof)
            do (eval-tlf form)))))


#+(or)
(with-environment (make-null-environment)
  (funcall (prepare-form '(funcall
                           (funcall
                            (lambda (x)
                              (lambda (y z)
                                (setq x (+ x (* y z)))
                                x))
                            3)
                           5 7)
                         (make-null-context))))

#+(or)
(with-environment (make-null-environment)
  (funcall (funcall
            (prepare-form
             '(lambda (a b &optional c (d 10 dp) &rest r &key e (f 12 fp) (g 12 gp) &aux (h 1) (i 2))
               (list a b c d dp e f fp g gp r h i))))
           1 2 3 4 :f 5 :e 6))
;; => (1 2 3 4 T 6 5 T 12 NIL (:F 5 :E 6) 1 2)
