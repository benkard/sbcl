(in-package "SB!EVAL2")

(defmacro declaim-optimizations ()
  `(declaim (optimize (debug 3) (space 2) (speed 2) (safety 0) (compilation-speed 0))))

(declaim-optimizations)

(defvar *dump-info* nil)
(defvar *set-info* nil)
(defvar *source-paths&locations* (make-hash-table :weakness :key
                                                  :test #'eq
                                                  :synchronized t))

(defparameter *debug-interpreter* nil)

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

(defmacro eval-lambda (lambda-list (&optional kind current-path source-loc) &body body)
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
  `(make-minimally-compiled-function
    ,name ,lambda-list ,doc ,source-loc ,current-path
    (sb!int:named-lambda minimally-compiled-function (sb!int:&more *more* *argnum*)
      (declare (optimize sb!c::store-closure-debug-pointer))
      ,@body)))

(declaim (inline get-arg))
(defun get-arg (i)
  (sb!c:%more-arg *more* i))

(declaim (inline get-arglist))
(defun get-arglist ()
  (multiple-value-list (sb!c:%more-arg-values *more* *argnum*)))

(defun current-path ()
  (when (boundp 'sb!c::*current-path*)
    sb!c::*current-path*))

(defun current-location ()
  (when (and (current-path)
             (typep (car (last (current-path)))
                    '(or fixnum null)))
    (sb!c::make-definition-source-location)))

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

(defun native-environment->context (lexenv)
  (declare (ignore lexenv))
  ;;FIXME
  (make-null-context))
(defun context->native-environment (context)
  (etypecase context
    (null
     (sb!c::make-null-lexenv))
    (context
     (let ((macros
             (loop for (name . expander) in (context-macros context)
                   collect `(,name . (sb!c::macro . ,expander))))
           (symbol-macros
             (loop for (name . form) in (context-symbol-macros context)
                   collect `(,name . (sb!c::macro . ,form))))
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
(defun globally-special-p (var)
  (eq :special (sb!int:info :variable :kind var)))
(defun globally-constant-p (var)
  (eq :constant (sb!int:info :variable :kind var)))
(defun symbol-macro-p (var)
  (eq :macro (sb!int:info :variable :kind var)))

(declaim (inline find-fdefn))
(defun find-fdefn (function-name)
  (sb!c::fdefinition-object function-name t))

(declaim (inline fdefn-fun))
(defun fdefn-fun (fdefn)
  (sb!c::fdefn-fun fdefn))


(defvar *vcode-form-debug-info-mapping*
  (make-hash-table :test 'eq :weakness :key))

(defun (setf vcode-form-debug-info) (val form)
  (setf (gethash form *vcode-form-debug-info-mapping*) val))

(defun vcode-form-debug-info (form)
  (gethash form *vcode-form-debug-info-mapping*))

(defun attach-debug-info (form current-path)
  (setf (vcode-form-debug-info form) current-path))

(defun compile-form (form
                     &optional (mode      *mode*)
                     &aux      (*mode*    :execute)
                               (sb!c::*current-path*
                                (when (and (boundp 'sb!c::*source-paths*)
                                           (or (sb!c::get-source-path form)
                                               (boundp 'sb!c::*current-path*))
                                           (sb!c::source-form-has-path-p form))
                                  (sb!c::ensure-source-path form))))
  (let ((compiled-form (%compile-form form mode)))
    (when (and (current-path) (current-location))
      (attach-debug-info compiled-form (cons (current-path) (current-location))))
    compiled-form))

(declaim (ftype (function (*) eval-closure) prepare-form))
(defun prepare-form (vcode)
  (let* ((eval-closure (%prepare-form vcode))
         (path&location (vcode-form-debug-info vcode)))
    (setf (source-path&location eval-closure) path&location)
    eval-closure))
