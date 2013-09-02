(in-package "SB!EVAL2")

(declaim (optimize (debug 2) (space 2) (speed 2) (safety 0) (compilation-speed 0)
                   (sb!c::store-closure-debug-pointer 3)))

(defvar *source-paths&locations* (make-hash-table :weakness :key :test #'eq))
(defparameter *debug-interpreter* nil)

(defun interpreted-function-source-location (function)
  (cdr (source-path&location function)))
(defun source-path (closure)
  (car (source-path&location closure)))
(defun source-location (closure)
  (cdr (source-path&location closure)))
(defun source-path&location (closure)
  (gethash closure *source-paths&locations*))
(defun (setf source-path&location) (val closure)
  (setf (gethash closure *source-paths&locations*) val))

(defun annotate-lambda-with-source (closure &optional
                                            (current-path
                                             (when (boundp 'sb!c::*current-path*)
                                               sb!c::*current-path*))
                                            (source-location
                                             (when (and current-path
                                                        (typep (car (last current-path))
                                                               '(or fixnum null)))
                                               (sb!c::make-definition-source-location))))
  (when source-location
    ;; XXX It's strange that (car (last sb!c::*current-path*)) can
    ;; ever be a non-fixnum.  This seemingly occurs only in the
    ;; context of #. evaluation (where *source-path* etc. are bound
    ;; but not relevant for the form we are processing).
    (setf (source-path&location closure) (cons current-path source-location)))
  closure)
(defun annotate-interpreted-lambda-with-source (closure current-path source-location)
  (declare (ignorable current-path source-location))
  (annotate-lambda-with-source closure current-path source-location)
  closure)
(defmacro eval-lambda (lambda-list (&optional kind current-path source-loc) &body body)
  `(annotate-lambda-with-source
    (sb!int:named-lambda ,(if kind
                              `(eval-closure ,kind)
                              'eval-closure)
                         ,lambda-list
      ,@body)
    ,current-path
    ,source-loc))
(defmacro interpreted-lambda ((name current-path source-loc) lambda-list &body body)
  (declare (ignore name))
  `(annotate-interpreted-lambda-with-source
    (sb!int:named-lambda interpreted-function ,lambda-list
      (declare (optimize sb!c::store-closure-debug-pointer))
      ,@body)
    ,current-path
    ,source-loc))

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
  (let ((functions
          (loop for (name . expander) in (context-collect context 'context-macros)
                collect `(,name . (sb!c::macro . ,expander))))
        (vars
          (loop for (name . form) in (context-collect context 'context-symbol-macros)
                collect `(,name . (sb!c::macro . ,form)))))
    (sb!c::internal-make-lexenv functions vars nil nil nil nil nil nil nil nil nil)))
(defun globally-special-p (var)
  (eq :special (sb!int:info :variable :kind var)))
(defun globally-constant-p (var)
  (eq :constant (sb!int:info :variable :kind var)))
(defun symbol-macro-p (var)
  (eq :macro (sb!int:info :variable :kind var)))
