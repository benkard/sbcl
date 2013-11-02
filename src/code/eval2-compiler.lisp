(in-package "SB!EVAL2")

;;;; THE COMPILER
;;;
;;; The eval2 compiler (more precisely, the COMPILE-FORM function)
;;; takes a Lisp form and a lexical context consisting of compile-time
;;; information (such as lexical variable information and
;;; declarations), and returns a corresponding form in VM code to be
;;; processed further by the PREPARE-FORM function in eval2.lisp.
;;;
;;; The lexical context is passed through the special variable
;;; *CONTEXT*.
;;;
;;; VM code is a fully macroexpanded, simplified form of Lisp code
;;; that lacks lexical binding forms, TAGBODY/GO, BLOCK/RETURN-FROM,
;;; macros, and symbol macros.  To implement lexical binding forms, it
;;; manages the environment explicitly.  VM code is designed to be
;;; interpretable using only immediately local information + an
;;; environment object, such that the interpreter does not need to
;;; track any context information (such as block tags, the names of
;;; lexical variables, etc.).
;;;
;;; VM code forms are nested forms consisting of a number of
;;; primitives.  A list of the supported primitives follows.  We write
;;; <foo> to indicate a literal argument, and define [[foo]] to mean
;;; the result of the evaluation of the form foo.
;;;
;;;
;;;   %arg-count
;;;
;;;     In the dynamic context of a %LAMBDA, returns the number of
;;;     arguments passed.
;;;
;;;
;;;   (%get-var <sym>)
;;;
;;;     Read the SYMBOL-VALUE of a special variable.
;;;
;;;
;;;   (%set-var <sym> valform)
;;;
;;;     Set the SYMBOL-VALUE of SYM to the result of [[valform]].
;;;
;;;
;;;   (%push-var <sym> valform)
;;;
;;;     PUSH [[valform]] onto (SYMBOL-VALUE <sym>).
;;;     This is basically a performance hack we use in the compiler.
;;;
;;;
;;;   (%get-in-env <nesting> <offset>)
;;;
;;;     Get the value of the lexical variable at <nesting>/<offset> in
;;;     the environment.
;;;
;;;
;;;   (%set-in-env <nesting> <offset> valform)
;;;
;;;     Set the value of the lexical variable at <nesting>/<offset> in
;;;     the environment to [[valform]].
;;;
;;;
;;;   (%with-environment <extent> <set-box-p> <debug-info> . body)
;;;
;;;     Set up a new lexical environment and evaluate BODY within it.
;;;     <extent> is one of :DYNAMIC and :INDEFINITE, indicating
;;;     whether the environment may be stack- allocated.  <set-box-p>
;;;     is a boolean indicating whether the environment corresponds to
;;;     a lambda.  In this case, *ENVBOX* is to be set to point to the
;;;     new environment, which is used by the debbuger to access
;;;     function call information.
;;;
;;;
;;;   (%get-arg <i>)
;;;
;;;     In the dynamic context of a %LAMBDA, fetch the I'h argument.
;;;
;;;
;;;   (%fetch-args <n>)
;;;
;;;     In the dynamic context of a %LAMBDA, fetch the first N
;;;     arguments and put them into the first N lexical variable slots
;;;     in the currently active environment.
;;;
;;;     This is a major optimization in the common case of setting up
;;;     a bunch of non-optional positional arguments as lexical
;;;     variables.
;;;
;;;
;;;   (%arglist-from <n>)
;;;
;;;     In the dynamic context of a %LAMBDA, get a LIST of arguments,
;;;     skipping the first N variables.
;;;
;;;
;;;   (%check-args <min> [<max>])
;;;
;;;     In the dynamic context of a %LAMBDA, check that the number of
;;;     arguments is (>= MIN) and (<= MAX).
;;;
;;;
;;;   (%check-key-args <positional-num>)
;;;
;;;     In the dynamic context of a %LAMBDA, check that the number of
;;;     keyword arguments is even, given the number of expected
;;;     positional arguments (required + optional) as
;;;     <positional-num>.
;;;
;;;
;;;   (%fdef-ref <function-name>)
;;;
;;;     Access (FDEFINITION FUNCTION-NAME).
;;;
;;;
;;;   (%local-call <nesting> <offset> . args)
;;;
;;;     Call the local function stored in the environment at
;;;     <nesting>/<offset> with the arguments [[args]].
;;;
;;;
;;;   (%global-call <function-name> . args)
;;;
;;;     Call the global function designated by <function-name> with
;;;     the arguments [[args]].
;;;
;;;
;;;   (%tagbody <catch-tag> . blocks)
;;;
;;;     Set up a loop that successively proceeds through the BLOCKS
;;;     (which are implicit progns of VM code) and either:
;;;
;;;       1. catches an integer N under the <catch-tag>, in which case
;;;          it jumps to block #N and proceeds from there, or
;;;
;;;       2. falls through the last block, in which case it terminates
;;;          and returns NIL.
;;;
;;;
;;;   (%lambda (<name> <current-path> <source-info> <lambda-list> <doc>) . body)
;;;
;;;     Create a funcallable MINIMALLY-COMPILED-FUNCTION that executes
;;;     BODY in an implicit progn and returns the result.  The options
;;;     given in the first argument to %LAMBDA are associated with the
;;;     MINIMALLY-COMPILED-FUNCTION for access by the debugger or
;;;     other facilities.
;;;
;;;
;;;   (load-time-value form)
;;;
;;;     Evaluate FORM at load-time (i.e., during the execution of
;;;     PREPARE-FORM) and return the result.
;;;
;;;
;;;   (%with-binding <var> val . body)
;;;
;;;     Set up a dynamic binding for [[val]] at the symbol <var> and
;;;     execute BODY in an implicit progn, returning its results.
;;;
;;;     This is effectively a special case of PROGV for a single
;;;     variable determined at compile-time.
;;;
;;;
;;;  In addition, the following Common Lisp forms are valid VM forms.
;;;  They are equivalent to their Common Lisp counterparts.
;;;
;;;   (catch tag . body)
;;;   (if a b c)
;;;   (multiple-value-call f . args)
;;;   (multiple-value-prog1 values-form . body)
;;;   (progn . body)
;;;   (progv vals vars . body)
;;;   (quote <object>)
;;;   (the <type> valform)
;;;   (throw tag thing)
;;;   (unwind-protect protected body)
;;;



;;;; Utilities
(defun assume-special (context var)
  "Signal a warning if VAR is unknown in CONTEXT."
  (unless (or (globally-special-p var)
              (context-var-special-p context var))
    (warn 'simple-warning
          :format-control "Undefined variable: ~S"
          :format-arguments (list var))))

(defun prevent-constant-modification (var)
  "Signal a warning if VAR is a constant."
  (when (globally-constant-p var)
    (warn "~S is a constant and thus can't be set." var)))


;;;; Component compilers
(defun compile-nil ()
  ''nil)

(defun compile-progn (forms &optional (*mode* *mode*))
  `(progn ,@(mapcar #'compile-form forms)))

(defun compile-macro-lambda (name lambda-form)
  "Compile a macro lambda form for MACROLET.

The result is a %LAMBDA VM code form for the macroexpander."
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

(defun compile-lambda (lambda-form &key (name nil) (blockp nil))
  "Compile a lambda with an optional block and name.

The result is a %LAMBDA VM code form for the supplied lambda expression."
  (destructuring-bind (lambda-list &rest exprs) lambda-form
    (with-parsed-body (body specials) exprs
      (multiple-value-bind (required optional restp rest keyp keys allowp auxp aux
                            morep more-context more-count)
          (parse-lambda-list lambda-list)
        (declare (ignore more-context more-count))
        (declare (ignorable auxp morep))
        (setq rest (or rest (gensym "REST")))
        (let* ((required-num (length required))
               (optional-num (length optional))
               (varspecs (list)))
          (setq varspecs (nreverse varspecs))
          (let* ((i 0))
            `(%lambda (,name ,(current-path) ,(current-location) ,lambda-list nil)
               ,(compile-form
                 `(%let* (,lambda-list ,name t)
                         ;; If all REQUIRED variables that we're
                         ;; binding are lexical, we can use
                         ;; %FETCH-ARGS to set them all at once.
                         ,(if (disjointp specials required)
                              `(,required  ;this instructs %let* to
                                           ;skip binding the REQUIRED
                                           ;variables
                                (%fetch-args ,required-num))
                              nil)
                         (;; required arguments (unless skipped by the above)
                          ,@(loop for arg in required
                                  collect `(,arg (%get-arg ,i))
                                  do (incf i))
                          ;; optionals
                          ,@(loop for arg in optional
                                  for var = (lambda-binding-main-var arg)
                                  for default = (lambda-binding-default arg)
                                  for suppliedp = (lambda-binding-suppliedp-var arg)
                                  collect `(,var (if (< ,i %arg-count)
                                                     (%get-arg ,i)
                                                     ,default))
                                  when suppliedp
                                  collect `(,suppliedp (< ,i %arg-count))
                                  do (incf i))
                          ;; rest list
                          ,@(when (or restp keyp)
                              `((,rest (%arglist-from ,i))
                                ,@(when keyp
                                    `((,(gensym)
                                       (%check-key-args
                                        ,(+ required-num optional-num)))))))
                          ;; keyword arguments
                          ,@(loop for arg in keys
                                  for var = (lambda-binding-main-var arg)
                                  for key = (lambda-key arg)
                                  for default = (lambda-binding-default arg)
                                  for suppliedp = (lambda-binding-suppliedp-var arg)
                                  collect `(,var (lazy-getf ,rest ',key ,default))
                                  when suppliedp
                                  collect `(,suppliedp
                                            (and (get-properties ,rest '(,key)) t))
                                  do (incf i))
                          ;; &aux bindings
                          ,@(loop for arg in aux
                                  for var = (lambda-binding-main-var arg)
                                  for default = (lambda-binding-default arg)
                                  collect `(,var ,default)))
                         (declare (special ,@specials))
                         (%check-args ,required-num
                                      ,(unless (or keyp restp) (+ required-num optional-num)))
                         ,@(when (and keyp (not allowp))
                             ;; check validity of keyword arguments
                             `((unless (getf ,rest :allow-other-keys nil)
                                 (let ((to-check ,rest))
                                   (tagbody
                                    check
                                      (unless (endp to-check)
                                        (let ((k (pop to-check)))
                                          (unless (member k ',(cons :allow-other-keys (mapcar #'lambda-key keys)))
                                            (error 'simple-program-error
                                                   :format-control "unknown &KEY argument: ~A"
                                                   :format-arguments (list k))))
                                        (pop to-check)
                                        (go check)))))))
                         (,@(if blockp `(%block ,(fun-name-block-name name)) `(progn))
                          ,@body))))))))))

(defun compile-ref (var)
  "Compile a variable reference.

The result is a VM code form for reading the variable.

VAR can be the name of a special or *CONTEXT*-local variable."
  (if (context-var-lexical-p *context* var)
      (let* ((lexical (context-find-lexical *context* var))
             (nesting (lexical-nesting lexical))
             (offset (lexical-offset lexical)))
        `(%get-in-env ,nesting ,offset))
      (if (globally-constant-p var)
          `(%get-var ,var)
          (progn
            (assume-special *context* var)
            `(%get-var ,var)))))

(defun compile-function-ref (function-name)
  "Compile a function reference.

FUNCTION-NAME can designate a local or global function."
  (if (local-function-p *context* function-name)
      (compile-ref `(function ,function-name))
      `(%fdef-ref ,function-name)))

(defun compile-local-call (f args)
  "Compile a call to the locally defined function named by F."
  (let* ((lexical (context-find-lexical *context* `(function ,f)))
         (nesting (lexical-nesting lexical))
         (offset (lexical-offset lexical)))
    `(%local-call ,nesting ,offset ,@(mapcar #'compile-form args))))

(defun compile-global-call (f args)
  "Compile a call to the global function named by F."
  (let ((args* (mapcar #'compile-form args)))
    `(%global-call ,f ,@args*)))

(defun %compile-form (form mode)
  (let ((vcode
          (%%compile-form form mode)))
    (cond
      ((and (member mode '(:compile-time-too :execute-tlf))
            (not (and (consp form)
                      (or
                       ;; specially processed toplevel form?
                       (member (first form)
                               '(progn locally macrolet symbol-macrolet
                                 eval-when))
                       ;; local macro?
                       (context-find-macro *context* (first form))
                       ;; global macro?
                       (and (symbolp (first form))
                            (macro-function (first form)))))))
       (funcall (prepare-form vcode) (make-null-environment))
       (ecase mode
         (:compile-time-too
          vcode)
         (:execute-tlf
          (compile-nil))))
      (t
       vcode))))

(defun %%compile-form (form mode)
  "Compile FORM into VM code in compilation mode MODE.

FORM must be a valid Common Lisp form within the lexical context
*CONTEXT*.

MODE controls the processing mode.  It must be one of

 - :EXECUTE (which enables non-toplevel compilation)
 - :EXECUTE-TLF (for toplevel forms read from source code)
 - :COMPILE-TIME-TOO (set by EVAL-WHEN)
 - :NOT-COMPILE-TIME (for toplevel forms read from a FASL)

Do not call this function directly.  Call COMPILE-FORM instead."
  (check-type *context* context)
  (values
   (cond
     ((self-evaluating-p form)
      `',form)
     (t
      (etypecase form
        (symbol
         (case form
           ((%arg-count)
            form)
           (otherwise
            (let ((local-macro? (context-find-symbol-macro *context* form)))
              (cond (local-macro?
                     (compile-form (car local-macro?) mode))
                    ((symbol-macro-p form)
                     (macroexpand-1 form (context->native-environment *context*)))
                    (t
                     (compile-ref form)))))))
        (cons
         (case (first form)
           ((%get-arg %arglist-from %get-var %get-in-env %fdef-ref %set-envbox
             %check-args %check-key-args)
            form)
           ((%set-var)
            (destructuring-bind (var val) (rest form)
              `(%set-var ,var ,(compile-form val))))
           ((%push-var)
            (destructuring-bind (val var) (rest form)
              `(%push-var ,(compile-form val) ,var)))
           ((%set-in-env)
            (destructuring-bind (nesting offset val) (rest form)
              `(%set-in-env ,nesting ,offset ,(compile-form val))))
           ((%with-binding)
            (destructuring-bind (var val &body body) (rest form)
              `(%with-binding ,var ,val ,(mapcar #'compile-form body))))
           ((%with-environment)
            (destructuring-bind (extent box-p info &rest body) (rest form)
              `(%with-environment ,extent ,box-p ,info ,@(mapcar #'compile-form body))))
           ((%local-call)
            (destructuring-bind (nesting offset &rest args) (rest form)
              `(%local-call ,nesting ,offset ,@(mapcar #'compile-form args))))
           ((%global-call)
            (destructuring-bind (name &rest args) (rest form)
              `(%global-call ,name ,@(mapcar #'compile-form args))))
           ((%lambda)
            (destructuring-bind (info &rest body) (rest form)
              `(%lambda ,info ,@(mapcar #'compile-form body))))
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
                   (#.*impl-named-lambda-syms*
                    (compile-lambda (cddr fun-form) :name (cadr fun-form)))
                   (t
                    (verify-function-name fun-form)
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
                              (eval `(progn ,@body))
                              (compile-nil))
                             ((and e (eq mode :compile-time-too))
                              (eval `(progn ,@body))
                              (compile-nil))
                             (t
                              (compile-nil)))))
                    ((or (member :execute times)
                         (member 'cl:eval times))
                     (compile-progn body mode))
                    (t
                     (compile-nil)))))
           ((setq)
            `(progn
               ,@(loop for (var valform) on (rest form) by #'cddr
                       collect
                          (cond ((context-var-symbol-macro-p *context* var)
                                 (let ((form (car (context-find-symbol-macro *context* var))))
                                   (compile-form `(setf ,form ,valform))))
                                ((context-var-lexical-p *context* var)
                                 (let* ((lexical (context-find-lexical *context* var))
                                        (nesting (lexical-nesting lexical))
                                        (offset  (lexical-offset lexical)))
                                   (compile-form
                                    `(%set-in-env ,nesting ,offset ,valform))))
                                (t
                                 (assume-special *context* var)
                                 (prevent-constant-modification var)
                                 (compile-form
                                  `(%set-var ,var ,valform)))))))
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
                  `(%with-environment :indefinite-extent nil (,debug-info ,varnum)
                     ,@(loop for (name lambda-list . body) in bindings
                             for i from 0
                             collect
                                `(%set-in-env 0 ,i
                                              ,(with-context binding-context
                                                 (compile-lambda (cons lambda-list body)
                                                                 :name name
                                                                 :blockp t))))
                     ,(with-context body-context
                        (compile-progn body)))))))
            ((let)
             (compile-form `(%let (:none nil) () ,@(rest form))))
            ((let*)
             (compile-form `(%let* (:none nil) () ,@(rest form))))
            ((%let %let*)
             (destructuring-bind ((lambda-list function-name &optional set-box-p)
                                  (&optional noinit-vars &rest init-block)
                                  bindings &rest exprs)
                 (rest form)
               (with-parsed-body (body specials) exprs
                 (let* ((real-bindings (mapcar (lambda (form)
                                                 (if (listp form)
                                                     (cons (first form) (second form))
                                                     (cons form nil)))
                                               bindings))
                        (vars (mapcar #'car real-bindings))
                        (varnum (length vars))
                        (binding-context
                          (context-add-env-lexicals *context* (list)))
                        (body-context
                          (if (eq (first form) '%let)
                              (context-add-env-lexicals *context* (list))
                              binding-context))
                        (debug-info
                          (make-debug-record body-context lambda-list function-name))
                        (dynamic-block-p
                          (and (eq (first form) '%let)
                               (or specials
                                   (some #'globally-special-p vars)))))
                   (with-context binding-context
                     `(%with-environment :indefinite-extent ,set-box-p (,debug-info ,varnum)
                        (,@(if dynamic-block-p
                               `(progv '(*dyn-vars* *dyn-vals*) '(nil nil))
                               `(progn))
                         ,@init-block
                         ,@(nlet iter ((remaining-bindings real-bindings))
                             (if (endp remaining-bindings)
                                 (let ((real-body-context
                                         (context-add-specials body-context specials)))
                                   (if dynamic-block-p
                                       `((progv (%get-var *dyn-vars*)
                                                (%get-var *dyn-vals*)
                                           ,(with-context real-body-context
                                              (compile-progn body))))
                                       `(,(with-context real-body-context
                                            (compile-progn body)))))
                                 (destructuring-bind (var . value-form)
                                     (first remaining-bindings)
                                   (let ((val* (with-context binding-context
                                                 (compile-form value-form))))
                                     (if (or (member (the symbol var) specials)
                                             (globally-special-p var))
                                         (progn
                                           (context-add-special! body-context var)
                                           (if (eq (first form) '%let)
                                               `((%push-var ,val* *dyn-vals*)
                                                 (%push-var ',var *dyn-vars*)
                                                 ,@(iter (rest remaining-bindings)))
                                               `((%with-binding ,var ,val*
                                                                ,@(iter (rest remaining-bindings))))))
                                         (progn
                                           (context-add-env-lexical! body-context var)
                                           (let* ((lexical (context-find-lexical body-context var))
                                                  (nesting (lexical-nesting lexical))
                                                  (offset (lexical-offset lexical)))
                                             `(,@(unless (member var noinit-vars)
                                                   `((%set-in-env ,nesting ,offset ,val*)))
                                               ,@(iter (rest remaining-bindings)))))))))))))))))
            ((load-time-value)
             (destructuring-bind (form) (rest form)
               `(load-time-value ,(compile-form form))))
            ((locally)
             (destructuring-bind (&rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (with-context (context-add-specials *context* specials)
                   (compile-progn body mode)))))
            ((multiple-value-setq)
             (destructuring-bind (vars values-form) (rest form)
               (if vars
                   (compile-form `(values (setf (values ,@vars) ,values-form)))
                   (compile-form `(values ,values-form)))))
            ((multiple-value-bind)
             (destructuring-bind (vars values-form &rest exprs) (rest form)
               (with-parsed-body (body specials) exprs
                 (compile-form
                  (let ((rsym (gensym)))
                    `(multiple-value-call
                         (lambda (&optional ,@vars &rest ,rsym)
                           (declare (special ,@specials) (ignore ,rsym))
                           ,@body)
                       ,values-form))))))
            ((quote)
             form)
            (#.*impl-named-lambda-syms*
             (compile-lambda (cddr form) :name (cadr form)))
            (#.*impl-named-function-syms*
             (compile-lambda (cdaddr form) :name (cadr form)))
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
                 (let ((bindings (mapcar (lambda (macro-form)
                                           (cons (first macro-form)
                                                 (call-with-environment
                                                  (context-evaluation-environment *context*)
                                                  (prepare-form
                                                   (with-context
                                                       (context-evaluation-context
                                                        *context*)
                                                     (compile-macro-lambda
                                                      (first macro-form)
                                                      (rest macro-form)))))))
                                         bindings)))
                   (with-context (context-add-specials
                                  (context-add-macros *context* bindings)
                                  specials)
                     (compile-progn body mode))))))
            (#.`(compiler-let ,@*impl-compiler-let-syms*)
             (destructuring-bind (bindings &rest body) (rest form)
               (with-context (context-add-evaluation-bindings
                              *context*
                              (loop for x in bindings
                                    for var = (if (consp x) (car x) x)
                                    for form = (if (consp x) (cadr x) nil)
                                    collect
                                       `(,var
                                         . ,(call-with-environment
                                             (context-evaluation-environment *context*)
                                             (prepare-form
                                              (with-context (context-evaluation-context *context*)
                                                (compile-form form)))))))
                 (compile-progn body))))
            ((catch unwind-protect multiple-value-prog1 multiple-value-call progv
              throw)
             `(,(first form) ,@(mapcar #'compile-form (rest form))))
            ((the #!+sbcl sb!ext:truly-the)
             (compile-form (third form)))
            ((progn)
             (compile-progn (rest form) mode))
            ((block)
             (compile-form `(%block ,@(rest form)) mode))
            ((return-from)
             (compile-form `(%return-from ,@(rest form)) mode))
            ((go)
             (compile-form `(%go ,@(rest form)) mode))
            ((tagbody)
             (compile-form `(%parsed-tagbody ,@(rest form)) mode))
            ((%tagbody)
             (destructuring-bind ((go-tag) &rest blocks) (rest form)
               `(%tagbody (,go-tag)
                  ,@(mapcar (lambda (forms) (mapcar #'compile-form forms)) blocks))))
            (otherwise
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
                     (funcall global-macro? form
                              (context->native-environment *context*))
                     mode))
                   ((and (listp f)
                         (eq 'lambda (first f)))
                    ;;transform into funcall
                    (compile-form
                     `(funcall #',f ,@args)
                     mode))
                   (t
                    (compile-global-call f args)))))))))))))

