(in-package #+sbcl "SB!EVAL2" #-sbcl "SB-EVAL2")

#+sbcl
(declaim (optimize (debug 2) (space 2) (speed 2) (safety 0) (compilation-speed 0)
                   (sb!c::store-closure-debug-pointer 3)))

(defvar *mode* :execute)
(defvar *env*)

(declaim (inline call-with-environment))
(declaim (ftype (function (environment function) *) call-with-environment))
(defun call-with-environment (env thunk)
  (let ((*env* env))
    (funcall thunk)))

;;(declaim (inline call-with-context))
(declaim (ftype (function (context function) *) call-with-context))
(defun call-with-context (context thunk)
  (let ((*context* context))
    (declare (special *context*))
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

(declaim (ftype (function (symbol) eval-closure) prepare-symbol-ref))
(defun prepare-symbol-ref (var)
  (eval-lambda ()
    (symbol-value var)))

(declaim (ftype (function (fixnum fixnum) eval-closure) prepare-lexical-ref))
(defun prepare-lexical-ref (nesting offset)
  (eval-lambda ()
    (environment-value *env* nesting offset)))

(declaim (ftype (function (fixnum fixnum *) eval-closure) prepare-lexical-set))
(defun prepare-lexical-set (nesting offset val)
  (let ((val* (prepare-form val)))
    (eval-lambda ()
      (setf (environment-value *env* nesting offset) (funcall val*)))))


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


(declaim (ftype (function ((or symbol list)) eval-closure) prepare-fdef-ref))
(defun prepare-fdef-ref (function-name)
  #+sbcl
  (let ((f* (sb!c::fdefinition-object function-name t)))
    (eval-lambda ()
      (or (sb!c::fdefn-fun f*)
          (error 'undefined-function :name function-name))))
  #-sbcl
  (eval-lambda ()
    (fdefinition function-name)))

(declaim (ftype (function () eval-closure) prepare-nil))
(defun prepare-nil ()
  (eval-lambda () nil))

(declaim (ftype (function (fixnum fixnum list) eval-closure) prepare-local-call))
(defun prepare-local-call (nesting offset args)
  (let* ((args* (mapcar (lambda (form) (prepare-form form)) args)))
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

(declaim (ftype (function ((or symbol list) list) eval-closure) prepare-global-call))
(defun prepare-global-call (f args)
  (let ((args* (mapcar (lambda (form) (prepare-form form)) args))
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

(declaim (ftype (function (eval-closure list) eval-closure) prepare-direct-call))
(defun prepare-direct-call (f args)
  (let ((args* (mapcar (lambda (form) (prepare-form form)) args)))
    (eval-lambda ()
      (apply (the (or symbol function) (funcall (the eval-closure f)))
             (mapcar (lambda (x) (funcall (the eval-closure x))) args*)))))

(declaim (ftype (function (list)
                          (values eval-closure &rest nil))
                prepare-progn))
(defun prepare-progn (forms)
  (let ((body* (mapcar (lambda (form) (prepare-form form)) forms)))
    (if (null body*)
        (prepare-nil)
        (let ((forms* (butlast body*))
              (last-form* (first (last body*))))
          (eval-lambda ()
            (dolist (form* forms*)
              (funcall (the eval-closure form*)))
            (funcall (the eval-closure last-form*)))))))

(defun assume-special (context var)
  (unless (or (globally-special-p var)
              (context-var-special-p context var))
    (warn 'simple-warning
          :format-control "Undefined variable: ~S"
          :format-arguments (list var))))

(defun prevent-constant-modification (var)
  (when (globally-constant-p var)
    (warn "~S is a constant and thus can't be set." var)))


(defvar *args*)
(defvar *argnum*)
(defvar *more*)
(defvar *envbox*)

(declaim (ftype (function * eval-closure) prepare-lambda))
(defun prepare-lambda (body name current-path source-location)
  (declare (ignorable name current-path source-location))
  (let ((body* (prepare-progn body)))
    (eval-lambda (current-path source-location)
      (let ((env *env*)
            ;; ENVBOX holds a box that points to the lambda's body
            ;; environment.  It is set by the body %LET through the
            ;; use of %SET-ENVBOX.
            ;;
            ;; This is useful mainly for debugging purposes.
            (envbox (make-array '())))
        (interpreted-lambda (name current-path source-location)
                            #-sbcl (&rest *args*)
                            #+sbcl (sb!int:&more *more* *argnum*)
          ;;(declare (dynamic-extent *args*))
          (let ((*env* env)
                (*envbox* envbox)
                #-sbcl (*argnum* (length *args*)))
            (funcall body*)))))))

(declaim (ftype (function (*) eval-closure) prepare-form))
(defun prepare-form (form)
  ;;(declare (optimize speed (safety 0) (space 1) (debug 0)))
  (values
   (cond
     ((self-evaluating-p form)
      (eval-lambda () form))
     (t
      (etypecase form
        (symbol
         (ecase form
           ((%argnum)
            (eval-lambda () *argnum*))))
        (cons
         (case (first form)
           ((%with-environment)
            (destructuring-bind (extent set-box-p (debug-info varnum) &rest body) (rest form)
              (let ((body* (prepare-progn body)))
                (ecase extent
                  ((:indefinite-extent)
                   (eval-lambda ()
                     (with-indefinite-extent-environment (*env* debug-info *env* varnum)
                       (when set-box-p
                         (setf (aref (the (simple-array t ()) *envbox*)) *env*))
                       (funcall body*))))
                  ((:dynamic-extent)
                   (eval-lambda ()
                     (with-dynamic-extent-environment (*env* debug-info *env* varnum)
                       (when set-box-p
                         (setf (aref (the (simple-array t ()) *envbox*)) *env*))
                       (funcall body*))))))))
           ((%getarg)
            (destructuring-bind (i) (rest form)
              (eval-lambda ()
                #+sbcl (sb!c:%more-arg *more* i)
                #-sbcl (elt *args* i))))
           ((%fetchargs)
            (destructuring-bind (n) (rest form)
              (eval-lambda ()
                (dotimes (i n)
                  (setf (environment-value *env* 0 i)
                        #+sbcl (sb!c:%more-arg *more* i)
                        #-sbcl (elt *args* i))))))
           ((%arglistfrom)
            (destructuring-bind (i) (rest form)
              (eval-lambda ()
                #+sbcl (nthcdr i (multiple-value-list (sb!c:%more-arg-values *more* *argnum*)))
                #-sbcl (nthcdr i *args*))))
           ((%checkargs)
            (destructuring-bind (min &optional max)
                (rest form)
              (declare (fixnum min) (type (or fixnum null) max))
              (eval-lambda ()
                (let ((argnum *argnum*))
                  (declare (fixnum argnum))
                  (when (< argnum min)
                    (error 'simple-program-error
                           :format-control "invalid number of arguments: ~D (expected: >=~D)"
                           :format-arguments (list argnum min)))
                  (when (and max (> argnum max))
                    (error 'simple-program-error
                           :format-control "invalid number of arguments: ~D (expected: <=~D)"
                           :format-arguments (list argnum max)))))))
           ((%varget)
            (destructuring-bind (var) (rest form)
              (eval-lambda ()
                (unless (boundp var)
                  (error 'unbound-variable :name var))
                (symbol-value var))))
           ((%varset)
            (destructuring-bind (var val) (rest form)
              (let ((val* (prepare-form val)))
                (eval-lambda ()
                  (setf (symbol-value var) (funcall val*))))))
           ((%varpush)
            (destructuring-bind (val var) (rest form)
              (let ((val* (prepare-form val)))
                (eval-lambda ()
                  (unless (boundp var)
                    (error 'unbound-variable :name var))
                  (push (funcall val*) (symbol-value var))))))
           ((%envget)
            (destructuring-bind (nesting offset) (rest form)
              (prepare-lexical-ref nesting offset)))
           ((%envset)
            (destructuring-bind (nesting offset val) (rest form)
              (prepare-lexical-set nesting offset val)))
           ((%fdef-ref)
            (destructuring-bind (function-name) (rest form)
              (prepare-fdef-ref function-name)))
           ((%local-call)
            (destructuring-bind (nesting offset &rest args) (rest form)
              (prepare-local-call nesting offset args)))
           ((%global-call)
            (destructuring-bind (f &rest args) (rest form)
              (prepare-global-call f args)))
           ((if)
            (destructuring-bind (a b &optional c) (rest form)
              (let ((a* (prepare-form a))
                    (b* (prepare-form b))
                    (c* (prepare-form c)))
                (eval-lambda ()
                  (if (funcall a*) (funcall b*) (funcall c*))))))
           ((%lambda)
            (destructuring-bind ((name current-path source-info) &rest body)
                (rest form)
              (prepare-lambda body name current-path source-info)))
           ((catch)
            (destructuring-bind (tag &body body) (rest form)
              (let ((tag* (prepare-form tag))
                    (body* (prepare-progn body)))
                (eval-lambda ()
                  (catch (funcall tag*)
                    (funcall body*))))))
           ((declare)
            (warn "DECLARE in form context.")
            (prepare-nil))
           ((load-time-value)
            (let ((load-form (cadr form)))
              ;; FIXME?
              (prepare-form load-form)))
           ((multiple-value-call)
            (destructuring-bind (f &rest argforms) (rest form)
              (let ((f* (prepare-form f))
                    (argforms* (mapcar (lambda (x) (prepare-form x)) argforms)))
                (eval-lambda ()
                  (apply (funcall (the eval-closure f*))
                         (mapcan (lambda (arg)
                                   (multiple-value-list
                                    (funcall (the eval-closure arg))))
                                 argforms*))))))
           ((multiple-value-prog1)
            (destructuring-bind (values-form &body body) (rest form)
              (let ((values-form* (prepare-form values-form))
                    (body*        (prepare-progn body)))
                (eval-lambda ()
                  (multiple-value-prog1
                      (funcall values-form*)
                    (funcall body*))))))
           ((progn)
            (prepare-progn (rest form)))
           ((%loop)
            (let ((body* (prepare-progn (rest form))))
              (eval-lambda ()
                (loop (funcall body*)))))
           ((%with-binding)
            (destructuring-bind (var val &body body) (rest form)
              (let ((val* (prepare-form val))
                    (body* (prepare-progn body)))
                (eval-lambda ()
                  (progv (list var) (list (funcall val*))
                    (funcall body*))))))
           ((progv)
            (destructuring-bind (vals vars &body body) (rest form)
              (let ((vals* (prepare-form vals))
                    (vars* (prepare-form vars))
                    (body* (prepare-progn body)))
                (eval-lambda ()
                  (progv (funcall vals*) (funcall vars*)
                    (funcall body*))))))
           ((quote)
            (let ((quoted-object (cadr form)))
              (eval-lambda ()
                quoted-object)))
           ((the)
            (prepare-form (third form)))
           ((throw)
            (destructuring-bind (tag result) (rest form)
              (let ((tag*    (prepare-form tag))
                    (result* (prepare-form result)))
                (eval-lambda ()
                  (throw (funcall tag*) (funcall result*))))))
           ((unwind-protect)
            (destructuring-bind (protected &body body) (rest form)
              (let ((protected* (prepare-form  protected))
                    (body*      (prepare-progn body)))
                (eval-lambda ()
                  (unwind-protect (funcall protected*)
                    (funcall body*))))))
           #+sbcl
           ((sb!ext:truly-the)
            (prepare-form (third form)))
           #+sbcl
           ((sb!int:named-lambda)
            (prepare-lambda (cddr form) :name (cadr form)))
           #+ccl
           ((ccl:nfunction)
            (prepare-lambda (cdaddr form) :name (cadr form)))
           ((setq block flet labels let let* locally multiple-value-bind
             return-from symbol-macrolet macrolet go tagbody eval-when
             multiple-value-setq)
            (error "invalid form"))
           (otherwise
            (warn "bare global call")
            (destructuring-bind (f . args) form
              (prepare-global-call f args))))))))
   t))


#+(or)
(with-environment (make-null-environment)
  (funcall (prepare-form (with-context (make-null-context)
                           (compile-form
                            '(funcall
                              (funcall
                               (lambda (x)
                                 (lambda (y z)
                                   (setq x (+ x (* y z)))
                                   x))
                               3)
                              5 7))))))
;; => 38

#+(or)
(with-environment (make-null-environment)
  (funcall (funcall
            (prepare-form
             (with-context (make-null-context)
               (compile-form
                '(lambda (a b &optional c (d 10 dp) &rest r &key e (f 12 fp) (g 12 gp) &aux (h 1) (i 2))
                  (list a b c d dp e f fp g gp r h i))))))
           1 2 3 4 :f 5 :e 6))
;; => (1 2 3 4 T 6 5 T 12 NIL (:F 5 :E 6) 1 2)
