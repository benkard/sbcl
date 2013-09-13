(in-package "SB!EVAL2")

(declaim-optimizations)

;;;; EVAL-CLOSURE PREPARATION
;;;
;;; The PREPARE-{...} functions generate EVAL-CLOSUREs from VM code
;;; forms.  The resulting eval-closure is funcallable and takes an
;;; ENVIRONMENT object as its only argument.
;;;
;;; The usual way of executing minimally compiled code is thus:
;;;
;;;   Lisp source  ---COMPILE-FORM---> VM code
;;;   VM code      ---PREPARE-FORM---> eval-closure
;;;   eval-closure ---FUNCALL--->      result
;;;

(declaim (ftype (function (symbol) eval-closure) prepare-symbol-ref))
(defun prepare-symbol-ref (var)
  (eval-lambda (env) (%var-ref)
    (declare (ignore env))
    (symbol-value var)))

(declaim (ftype (function (fixnum fixnum) eval-closure) prepare-lexical-ref))
(defun prepare-lexical-ref (nesting offset)
  (eval-lambda (env) (%env-ref)
    (environment-value env nesting offset)))

(declaim (ftype (function (fixnum fixnum *) eval-closure) prepare-lexical-set))
(defun prepare-lexical-set (nesting offset val)
  (let ((val* (prepare-form val)))
    (eval-lambda (env) (%env-set)
      (setf (environment-value env nesting offset) (funcall val* env)))))

(declaim (ftype (function ((or symbol list)) eval-closure) prepare-fdef-ref))
(defun prepare-fdef-ref (function-name)
  (let ((f* (find-fdefn function-name)))
    (eval-lambda (env) (%fdef-ref)
      (declare (ignore env))
      (or (fdefn-fun f*)
          (error 'undefined-function :name function-name)))))

(declaim (ftype (function () eval-closure) prepare-nil))
(defun prepare-nil ()
  (eval-lambda (env) () (declare (ignore env)) nil))

(declaim (ftype (function (fixnum fixnum list) eval-closure) prepare-local-call))
(defun prepare-local-call (nesting offset args)
  (let* ((args* (map 'simple-vector #'prepare-form args)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          `(eval-lambda (env) (%local-call)
             (declare (ignorable env))
             (funcall (the function (environment-value env nesting offset))
                      ,@(loop for i from 0 below m%
                              collect `(funcall (the eval-closure (svref args* ,i))
                                                env)))))
        (eval-lambda (env) (%local-call)
          (apply (the function (environment-value env nesting offset))
                 (map 'list (lambda (x) (funcall (the eval-closure x) env)) args*))))))

(declaim (ftype (function ((or symbol list) list) eval-closure) prepare-global-call))
(defun prepare-global-call (f args)
  (let ((args* (map 'simple-vector #'prepare-form args))
        (f* (find-fdefn f)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          `(eval-lambda (env) (%global-call)
             (declare (ignorable env))
             (funcall (or (fdefn-fun f*)
                          (error 'undefined-function :name f))
                      ,@(loop for i from 0 below m%
                              collect
                                 `(funcall (the eval-closure (svref args* ,i))
                                           env)))))
        (eval-lambda (env) (%global-call)
          (apply (or (fdefn-fun f*)
                     (error 'undefined-function :name f))
                 (map 'list
                      (lambda (x) (funcall (the eval-closure x) env))
                      args*))))))

(declaim (ftype (function (list)
                          (values eval-closure &rest nil))
                prepare-progn))
(defun prepare-progn (forms)
  (let ((body* (mapcar (lambda (form) (prepare-form form)) forms)))
    (cond ((null body*)
           (prepare-nil))
          ((endp (rest body*))
           (first body*))
          (t
           (let ((forms* (butlast body*))
                 (last-form* (first (last body*))))
             (eval-lambda (env) (%progn)
               (dolist (form* forms*)
                 (funcall (the eval-closure form*) env))
               (funcall (the eval-closure last-form*) env)))))))

(declaim (ftype (function * eval-closure) prepare-lambda))
(defun prepare-lambda (body name current-path source-location lambda-list doc)
  "Generate an EVAL-CLOSURE that creates a MINIMALLY-COMPILED-FUNCTION with the supplied parameters.

In the MINIMALLY-COMPILED-FUNCTION, *ENV-BOX* gets bound to a box
that, when the MINIMALLY-COMPILED-FUNCTION is executed, is set to
point to the environment that corresponds to the call frame for this
call instance."
  (declare (ignorable name current-path source-location))
  (let ((body* (prepare-progn body)))
    (eval-lambda (env) (%lambda current-path source-location)
      (let (;; ENVBOX holds a box that points to the lambda's body
            ;; environment.  It is set by the body %LET.
            ;;
            ;; This is useful mainly for debugging purposes.
            (envbox (make-array '())))
        (interpreted-lambda (name current-path source-location lambda-list doc)
          (let ((*env-box* envbox))
            (funcall body* env)))))))

(declaim (ftype (function (*) eval-closure) %prepare-form))
(defun %prepare-form (form)
  "Compile the VM code form FORM into an executable EVAL-CLOSURE.

The result is an EVAL-CLOSURE that can be executed by funcalling it,
passing an ENVIRONMENT object as the argument."
  ;;(declare (optimize speed (safety 0) (space 1) (debug 0)))
  (values
   (cond
     ((self-evaluating-p form)
      (eval-lambda (env) (quote) (declare (ignore env)) form))
     (t
      (etypecase form
        (symbol
         (ecase form
           ((%arg-count)
            (eval-lambda (env) (%arg-count) (declare (ignore env)) *arg-count*))))
        (cons
         (case (first form)
           ((%with-environment)
            (destructuring-bind (extent set-box-p (debug-info varnum) &rest body) (rest form)
              (let ((body* (prepare-progn body)))
                (ecase extent
                  ((:indefinite-extent)
                   (eval-lambda (env) (%with-environment)
                     ;;(declare (notinline %make-environment))
                     (with-indefinite-extent-environment (env debug-info env varnum)
                       (when set-box-p
                         (setf (aref (the (simple-array t ()) *env-box*)) env))
                       (funcall body* env))))
                  ((:dynamic-extent)
                   (eval-lambda (env) (%with-environment)
                     (with-dynamic-extent-environment (env debug-info env varnum)
                       (when set-box-p
                         (setf (aref (the (simple-array t ()) *env-box*)) env))
                       (funcall body* env))))))))
           ((%get-arg)
            (destructuring-bind (i) (rest form)
              (eval-lambda (env) (%get-arg)
                (declare (ignore env))
                (get-arg i))))
           ((%fetch-args)
            (destructuring-bind (n) (rest form)
              (declare (fixnum n))
              (eval-lambda (env) (%fetch-args)
                (loop for i from 0 below (min n (the fixnum *arg-count*))
                      do (setf (environment-value env 0 i)
                               (get-arg i))))))
           ((%arglist-from)
            (destructuring-bind (i) (rest form)
              (eval-lambda (env) (%arglist-from)
                (declare (ignore env))
                (nthcdr i (get-arglist)))))
           ((%check-args)
            (destructuring-bind (min &optional max)
                (rest form)
              (declare (fixnum min) (type (or fixnum null) max))
              (eval-lambda (env) (%check-args)
                (declare (ignore env))
                (let ((arg-count *arg-count*))
                  (declare (fixnum arg-count))
                  (when (< arg-count min)
                    (error 'simple-program-error
                           :format-control "invalid number of arguments: ~D (expected: >=~D)"
                           :format-arguments (list arg-count min)))
                  (when (and max (> arg-count max))
                    (error 'simple-program-error
                           :format-control "invalid number of arguments: ~D (expected: <=~D)"
                           :format-arguments (list arg-count max)))))))
           ((%check-key-args)
            (destructuring-bind (positional-num)
                (rest form)
              (declare (fixnum positional-num))
              (eval-lambda (env) (%check-key-args)
                (let ((arg-count *arg-count*))
                  (declare (fixnum arg-count))
                  (when (and (> arg-count positional-num)
                             (oddp (- arg-count positional-num)))
                    (let ((rest (funcall
                                 (prepare-form `(%arglist-from ,positional-num))
                                 env)))
                      (error 'simple-program-error
                             :format-control "odd number of keyword arguments: ~S"
                             :format-arguments (list rest))))))))
           ((%get-var)
            (destructuring-bind (var) (rest form)
              (eval-lambda (env) (%varget)
                (declare (ignore env))
                (unless (boundp var)
                  (error 'unbound-variable :name var))
                (symbol-value var))))
           ((%set-var)
            (destructuring-bind (var val) (rest form)
              (let ((val* (prepare-form val)))
                (eval-lambda (env) (%varset)
                  (setf (symbol-value var) (funcall val* env))))))
           ((%push-var)
            (destructuring-bind (val var) (rest form)
              (let ((val* (prepare-form val)))
                (eval-lambda (env) (%varpush)
                  (unless (boundp var)
                    (error 'unbound-variable :name var))
                  (push (funcall val* env) (symbol-value var))))))
           ((%get-in-env)
            (destructuring-bind (nesting offset) (rest form)
              (prepare-lexical-ref nesting offset)))
           ((%set-in-env)
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
           ((%tagbody)
            (destructuring-bind ((go-tag) &rest blocks) (rest form)
              (let* ((blocks*
                       (map 'simple-vector #'prepare-progn blocks))
                     (block-count
                       (length blocks*)))
                (eval-lambda (env) (%tagbody)
                  (let ((continuation-index 0))
                    (declare (fixnum continuation-index))
                    (loop
                      until (= continuation-index block-count)
                      do (setq continuation-index
                               (catch go-tag
                                 (funcall (the eval-closure
                                               (svref blocks* continuation-index)) env)
                                 (1+ continuation-index)))))))))
           ((if)
            (destructuring-bind (a b &optional c) (rest form)
              (let ((a* (prepare-form a))
                    (b* (prepare-form b))
                    (c* (prepare-form c)))
                (eval-lambda (env) (if)
                  (if (funcall a* env) (funcall b* env) (funcall c* env))))))
           ((%lambda)
            (destructuring-bind ((name current-path source-info lambda-list doc)
                                 &rest body)
                (rest form)
              (prepare-lambda body name current-path source-info lambda-list doc)))
           ((catch)
            (destructuring-bind (tag &body body) (rest form)
              (let ((tag* (prepare-form tag))
                    (body* (prepare-progn body)))
                (eval-lambda (env) (catch)
                  (catch (funcall tag* env)
                    (funcall body* env))))))
           ((declare)
            (warn "DECLARE in form context.")
            (prepare-nil))
           ((load-time-value)
            (destructuring-bind (load-form) (rest form)
              (let ((thing
                      (call-with-environment
                       (make-null-environment)
                       (prepare-form
                        (with-context (make-null-context) (compile-form load-form))))))
                (eval-lambda (env) (load-time-value)
                  (declare (ignore env))
                  thing))))
           ((multiple-value-call)
            (destructuring-bind (f &rest argforms) (rest form)
              (let ((f* (prepare-form f))
                    (argforms* (mapcar (lambda (x) (prepare-form x)) argforms)))
                (eval-lambda (env) (multiple-value-call)
                  (apply (funcall (the eval-closure f*) env)
                         (mapcan (lambda (arg)
                                   (multiple-value-list
                                    (funcall (the eval-closure arg) env)))
                                 argforms*))))))
           ((multiple-value-prog1)
            (destructuring-bind (values-form &body body) (rest form)
              (let ((values-form* (prepare-form values-form))
                    (body*        (prepare-progn body)))
                (eval-lambda (env) (multiple-value-prog1)
                  (multiple-value-prog1
                      (funcall values-form* env)
                    (funcall body* env))))))
           ((progn)
            (prepare-progn (rest form)))
           ((%with-binding)
            (destructuring-bind (var val &body body) (rest form)
              (let ((val* (prepare-form val))
                    (body* (prepare-progn body)))
                (eval-lambda (env) (%with-binding)
                  (progv (list var) (list (funcall val* env))
                    (funcall body* env))))))
           ((progv)
            (destructuring-bind (vals vars &body body) (rest form)
              (let ((vals* (prepare-form vals))
                    (vars* (prepare-form vars))
                    (body* (prepare-progn body)))
                (eval-lambda (env) (progv)
                  (progv (funcall vals* env) (funcall vars* env)
                    (funcall body* env))))))
           ((quote)
            (let ((quoted-object (cadr form)))
              (eval-lambda (env) (quote)
                (declare (ignore env))
                quoted-object)))
           ((the)
            (prepare-form (third form)))
           ((throw)
            (destructuring-bind (tag result) (rest form)
              (let ((tag*    (prepare-form tag))
                    (result* (prepare-form result)))
                (eval-lambda (env) (throw)
                  (throw (funcall tag* env) (funcall result* env))))))
           ((unwind-protect)
            (destructuring-bind (protected &body body) (rest form)
              (let ((protected* (prepare-form  protected))
                    (body*      (prepare-progn body)))
                (eval-lambda (env) (unwind-protect)
                  (unwind-protect (funcall protected* env)
                    (funcall body* env))))))
           ((setq block flet labels let let* locally multiple-value-bind
             return-from symbol-macrolet macrolet go tagbody eval-when
             multiple-value-setq)
            (error "invalid form"))
           (otherwise
            (warn "bare global call")
            (destructuring-bind (f . args) form
              (prepare-global-call f args))))))))
   t))


;;;; UTILITY FUNCTIONS
;;;
;;; These replace CL:EVAL and CL:LOAD.  They are mainly suitable for
;;; debugging the evaluator or for use in implementations other than
;;; SBCL.
(defun eval2 (form &optional environment)
  (let ((context (if environment
                     (native-environment->context environment)
                     (make-null-context)))
        (env (make-null-environment)))
    (call-with-environment
     env
     (prepare-form (with-context context (compile-form form :execute))))))

(defun load2 (file)
  (if (streamp file)
      (loop with eof = (gensym)
            for form = (read file nil eof nil)
            until (eq form eof)
            when (listp form)
              do (format t "~&; (~S~:[~; ~S~:[~; ...~]~])"
                         (car form) (cdr form) (cadr form) (cddr form))
            do (funcall
                (prepare-form
                 (with-context (make-null-context)
                   (compile-form form :not-compile-time)))
                (make-null-environment)))
      (with-open-file (in file)
        (load2 in))))


;;;; EXAMPLES
#+(or)
(call-with-environment (make-null-environment)
  (prepare-form (with-context (make-null-context)
                  (compile-form
                   '(funcall
                     (funcall
                      (lambda (x)
                        (lambda (y z)
                          (setq x (+ x (* y z)))
                          x))
                      3)
                     5 7)))))
;; => 38

#+(or)
(funcall
 (call-with-environment (make-null-environment)
                        (funcall
                         (prepare-form
                          (with-context (make-null-context)
                            (compile-form
                             '(lambda (a b &optional c (d 10 dp) &rest r &key e (f 12 fp) (g 12 gp) &aux (h 1) (i 2))
                               (list a b c d dp e f fp g gp r h i))))))
                        1 2 3 4 :f 5 :e 6))
;; => (1 2 3 4 T 6 5 T 12 NIL (:F 5 :E 6) 1 2)

#+(or)
(with-context (make-null-context)
  (compile-form
   '(ccl:compiler-let ((x (+ 10 12)))
     (macrolet ((g () (setq x 100))
                (f () `(list ,x)))
       (g)
       (f)))))
