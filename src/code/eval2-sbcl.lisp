(in-package "SB!EVAL2")

(declaim (optimize (debug 2) (space 2) (speed 2) (safety 0) (compilation-speed 0)
                   (sb!c::store-closure-debug-pointer 3)))

(defvar *source-paths* (make-hash-table :weakness :key :test #'eq))
(defvar *source-info* (make-hash-table :weakness :key :test #'eq))
(defvar *source-locations* (make-hash-table :weakness :key :test #'eq))
(defvar *closure-tags* (make-hash-table :weakness :key :test #'eq))
(defvar *interpreted-functions* (make-hash-table :weakness :key :test #'eq))
(defparameter *debug-interpreter* nil)
(defun interpreted-function-source-location (function)
  (gethash function *source-locations* nil))
(defun interpreted-function-p (function)
  (gethash function *interpreted-functions* nil))
(defun (setf interpreted-function-p) (val function)
  (setf (gethash function *interpreted-functions*) (and val t)))
(defun source-path (eval-closure)
  (gethash eval-closure *source-paths*))
(defun source-info (eval-closure)
  (gethash eval-closure *source-info*))
(defun source-location (eval-closure)
  (gethash eval-closure *source-locations*))
(defun (setf source-path) (val eval-closure)
  (setf (gethash eval-closure *source-paths*) val))
(defun (setf source-info) (val eval-closure)
  (setf (gethash eval-closure *source-info*) val))
(defun (setf source-location) (val eval-closure)
  (setf (gethash eval-closure *source-locations*) val))


(defun annotate-lambda-with-source (closure)
  (when (and (boundp 'sb!c::*current-path*)
             (boundp 'sb!c::*source-info*)
             (typep (car (last sb!c::*current-path*)) '(or fixnum null)))
    ;; XXX It's strange that (car (last sb!c::*current-path*)) can
    ;; ever be a non-fixnum.  This seemingly occurs only in the
    ;; context of #. evaluation (where *source-info* etc. are bound
    ;; but not relevant for the form we are processing).
    (setf (source-path closure) sb!c::*current-path*)
    (setf (source-info closure) sb!c::*source-info*)
    (setf (source-location closure) (sb!c::make-definition-source-location)))
  closure)
(defun annotate-interpreted-lambda-with-source (closure current-path source-info)
  (when (and current-path source-info)
    (let ((sb!c::*current-path* current-path)
          (sb!c::*source-info* source-info))
      (annotate-lambda-with-source closure)))
  (setf (interpreted-function-p closure) t)
  closure)
(defmacro eval-lambda (lambda-list &body body)
  `(annotate-lambda-with-source
    (sb!int:named-lambda eval-closure ,lambda-list
      (declare (optimize sb!c::store-closure-debug-pointer debug (safety 0)))
      ,@body)))
(defmacro interpreted-lambda ((name current-path source-info) lambda-list &body body)
  (declare (ignore name))
  `(annotate-interpreted-lambda-with-source
    (sb!int:named-lambda interpreted-function ,lambda-list
      (declare (optimize sb!c::store-closure-debug-pointer))
      ,@body)
    ,current-path
    ,source-info))

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