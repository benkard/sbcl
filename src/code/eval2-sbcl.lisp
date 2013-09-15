(in-package "SB!EVAL2")

(defmacro declaim-optimizations ()
  `(declaim (optimize (debug 3) (space 2) (speed 2) (safety 0) (compilation-speed 0))))

(declaim-optimizations)


;;;; SETTINGS
(defparameter *debug-interpreter* nil
  "If true, preserve SB-EVAL2::EVAL-CLOSURE frames in stack traces.  Otherwise, generate human-readable stack frames of SB-EVAL2:MINIMALLY-COMPILED-FUNCTION calls suitable for debugging programs.")


;;;; COMPILE-TIME CONSTANTS
;;;
;;; These map implementation-specific symbols to compiler features.
;;;
;;; (It might be worthwhile to abstract the relevant parts of
;;; %COMPILE-FORM away in a more flexible way, such as by factoring
;;; all operators into separate definitions similar to the way
;;; SB-WALKER does it.)
;;;
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *impl-compiler-let-syms* '())
  (defvar *impl-named-lambda-syms* '(sb!int:named-lambda))
  (defvar *impl-named-function-syms* '())
  (defvar *impl-the-syms* '(sb!ext:truly-the)))


;;;; PREPARE-FORM UTILITIES
(defmacro eval-lambda (lambda-list (&optional kind current-path source-loc) &body body)
  "Create an EVAL-CLOSURE with body BODY and attach source code information."
  `(annotate-lambda-with-source
    (sb!int:named-lambda ,(if kind
                              `(eval-closure ,kind)
                              'eval-closure)
                         ,lambda-list
      (declare (optimize sb!c::store-closure-debug-pointer))
      ,@body)
    ,current-path
    ,source-loc))

(defmacro interpreted-lambda ((name current-path source-loc lambda-list doc)
                              &body body)
  "Create a MINIMALLY-COMPILED-FUNCTION object with body BODY and attach metainformation."
  `(make-minimally-compiled-function
    ,name ,lambda-list ,doc ,source-loc ,current-path
    (sb!int:named-lambda minimally-compiled-function (sb!int:&more *more* *arg-count*)
      (declare (optimize sb!c::store-closure-debug-pointer))
      ,@body)))


;;;; HOST INTEROPERABILITY
(defun native-environment->context (lexenv)
  (check-type lexenv sb!c::lexenv)
  (let ((native-funs (sb!c::lexenv-funs lexenv))
        (native-vars (sb!c::lexenv-vars lexenv)))
    ;; check taken from SB!EVAL::MAKE-ENV-FROM-NATIVE-ENVIRONMENT
    (flet ((is-macro (thing)
             (and (consp thing) (eq (car thing) 'sb!sys:macro))))
      (when (or (sb!c::lexenv-blocks lexenv)
                (sb!c::lexenv-cleanup lexenv)
                (sb!c::lexenv-lambda lexenv)
                (sb!c::lexenv-tags lexenv)
                (sb!c::lexenv-type-restrictions lexenv)
                (find-if-not #'is-macro native-funs :key #'cdr)
                (find-if-not #'is-macro native-vars :key #'cdr))
        (error 'compiler-environment-too-complex-error
               :format-control
               "~@<Lexical environment is too complex to evaluate in: ~S~:@>"
               :format-arguments
               (list lexenv))))
    (let ((context
            (make-null-context))
          (macros
            (loop for (name _ . expander) in native-funs
                  collect (cons name expander)))
          (symbol-macros
            (loop for (name _ . form) in native-vars
                  collect (cons name form))))
      (setf (context-macros context) macros
            (context-symbol-macros context) symbol-macros)
      context)))

(defun context->native-environment (context)
  (etypecase context
    (null
     (sb!c::make-null-lexenv))
    (context
     (let ((macros
             (loop for (name . expander) in (context-macros context)
                   collect `(,name . (sb!sys:macro . ,expander))))
           (symbol-macros
             (loop for (name . form) in (context-symbol-macros context)
                   collect `(,name . (sb!sys:macro . ,form))))
           (functions
             (loop for lexical in (context-lexicals context)
                   for name = (lexical-name lexical)
                   when (and (listp name) (eq 'function (car name)))
                     collect (let (leaf)  ;a null SB!C::FUNCTIONAL
                               `(,(second name) . ,leaf))))
           (vars
             (loop for lexical in (context-lexicals context)
                   for name = (lexical-name lexical)
                   unless (and (listp name) (eq 'function (car name)))
                     collect (let (leaf)  ;a null SB!C::LEAF
                               `(,name . ,leaf)))))
       (sb!c::make-lexenv :default (context->native-environment
                                    (context-parent context))
                          :funs (append macros functions)
                          :vars (append symbol-macros vars))))))


;;;; COMPILER UTILITIES
(defun verify-function-name (thing)
  "Signal an error if THING is not a valid function name."
  (assert (sb!int:valid-function-name-p thing)))

(defun globally-special-p (var)
  (eq :special (sb!int:info :variable :kind var)))

(defun globally-constant-p (var)
  (eq :constant (sb!int:info :variable :kind var)))

(defun symbol-macro-p (var)
  (eq :macro (sb!int:info :variable :kind var)))

(defun self-evaluating-p (form)
  (sb!int:self-evaluating-p form))

(defun fun-name-block-name (fun-name)
  (sb!int:fun-name-block-name fun-name))

(defun parse-macrolet-binding-form (lambda-list whole body name env)
  (sb!kernel:parse-defmacro lambda-list
                            whole
                            body
                            name
                            'macrolet
                            :environment env))

(defun parse-lambda-list (lambda-list)
  ;; returns values:
  ;;
  ;;   (required optional restp rest keyp keys allowp auxp aux morep
  ;;   more-context more-count)
  ;;
  (sb!int:parse-lambda-list lambda-list))


;;;; EFFICIENT FUNCTION ARGUMENT ACCESS
(declaim (inline get-arg))
(defun get-arg (i)
  (sb!c:%more-arg *more* i))

(declaim (inline get-arglist))
(defun get-arglist ()
  (multiple-value-list (sb!c:%more-arg-values *more* 0 *arg-count*)))


;;;; EFFICIENT ACCESS TO GLOBAL FUNCTION DEFINITIONS
(declaim (inline find-fdefn))
(defun find-fdefn (function-name)
  (sb!c::fdefinition-object function-name t))

(declaim (inline fdefn-fun))
(defun fdefn-fun (fdefn)
  (sb!c::fdefn-fun fdefn))


;;;; DEBUGGING INFORMATION TRACKING
(defvar *vcode-form-debug-info-mapping*
  (make-hash-table :test 'eq :weakness :key))

(defun (setf vcode-form-debug-info) (val form)
  (setf (gethash form *vcode-form-debug-info-mapping*) val))

(defun vcode-form-debug-info (form)
  (gethash form *vcode-form-debug-info-mapping*))

(defun attach-debug-info (form current-path)
  (setf (vcode-form-debug-info form) current-path))


;;;; SOURCE LOCATION TRACKING
(defvar *source-paths&locations* (make-hash-table :weakness :key
                                                  :test #'eq
                                                  :synchronized t))

(defun current-path ()
  (when (boundp 'sb!c::*current-path*)
    sb!c::*current-path*))

(defun current-location ()
  (when (and (current-path)
             (typep (car (last (current-path)))
                    '(or fixnum null)))
    (sb!c::make-definition-source-location)))

(defun source-path (closure)
  (car (source-path&location closure)))

(defun source-location (closure)
  (cdr (source-path&location closure)))

(defun source-path&location (closure)
  (progn ;;sb-ext:with-locked-hash-table (*source-paths&locations*)
    (gethash closure *source-paths&locations*)))

(defun (setf source-path&location) (val closure)
  (progn ;;sb-ext:with-locked-hash-table (*source-paths&locations*)
    (setf (gethash closure *source-paths&locations*) val)))

(defun annotate-lambda-with-source (closure current-path source-location)
  (when source-location
    ;; XXX It's strange that (car (last sb!c::*current-path*)) can
    ;; ever be a non-fixnum.  This seemingly occurs only in the
    ;; context of #. evaluation (where *source-path* etc. are bound
    ;; but not relevant for the form we are processing).
    (setf (source-path&location closure) (cons current-path source-location)))
  closure)


;;;; ENTRY POINT WRAPPERS
;;;
;;; These wrap %COMPILE-FORM and %PREPARE-FORM to attach debugging
;;; information to the results.
;;;
(defun compile-form (form
                     &optional (mode      *mode*)
                     &aux      (*mode*    :execute)
                               (sb!c::*current-path*
                                (when (and (boundp 'sb!c::*source-paths*)
                                           (or (sb!c::get-source-path form)
                                               (boundp 'sb!c::*current-path*))
                                           (sb!c::source-form-has-path-p form))
                                  (sb!c::ensure-source-path form))))
  "Compile FORM into VM code in compilation mode MODE.

See %COMPILE-FORM for more detailed documentation."
  (let ((compiled-form (%compile-form form mode)))
    (when (and (current-path) (current-location))
      (attach-debug-info compiled-form (cons (current-path) (current-location))))
    compiled-form))

(declaim (ftype (function (*) eval-closure) prepare-form))
(defun prepare-form (vcode)
  "Compile VCODE from VM code into a funcallable evaluator for VCODE.

See %PREPARE-FORM for more detailed documentation."
  (let* ((eval-closure (%prepare-form vcode))
         (path&location (vcode-form-debug-info vcode)))
    (setf (source-path&location eval-closure) path&location)
    eval-closure))
