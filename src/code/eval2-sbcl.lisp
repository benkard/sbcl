(in-package "SB!EVAL2")

(declaim (optimize (debug 2) (space 2) (speed 2) (safety 0) (compilation-speed 0)
                   (sb!c::store-closure-debug-pointer 3)))

(defvar *dump-info* nil)
(defvar *set-info* nil)
(defvar *source-paths&locations* (make-hash-table :weakness :key
                                                  :test #'eq
                                                  :synchronized t))

(defparameter *debug-interpreter* nil)

(defun interpreted-function-p (function)
  (and (sb!kernel:closurep function)
       (eq 'interpreted-function (sb!kernel:%fun-name (sb!kernel:%fun-fun function)))))

(defun interpreted-function-name (function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :name))
    (funcall function)))
(defun (setf interpreted-function-name) (val function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :set-name)
        (*set-info* val))
    (funcall function)))
(defun interpreted-function-doc (function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :doc))
    (funcall function)))
(defun (setf interpreted-function-doc) (val function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :set-doc)
        (*set-info* val))
    (funcall function)))
(defun interpreted-function-lambda-list (function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :lambda-list))
    (funcall function)))
(defun (setf interpreted-function-lambda-list) (val function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :set-lambda-list)
        (*set-info* val))
    (funcall function)))
(defun interpreted-function-source-location (function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :source-location))
    (funcall function)))
(defun interpreted-function-source-path (function)
  (assert (interpreted-function-p function))
  (let ((*dump-info* :source-path))
    (funcall function)))

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
      ,@body)
    ,current-path
    ,source-loc))

(defmacro interpreted-lambda ((name current-path source-loc lambda-list doc)
                              real-lambda-list &body body)
  (let ((name%         (gensym "NAME"))
        (lambda-list%  (gensym "LAMBDA-LIST"))
        (doc%          (gensym "DOC"))
        (current-path% (gensym "CURRENT-PATH"))
        (source-loc%   (gensym "SOURCE-LOCATION")))
    `(let ((,name%         ,name)
           (,lambda-list%  ,lambda-list)
           (,doc%          ,doc)
           (,source-loc%   ,source-loc)
           (,current-path% ,current-path))
       (sb!int:named-lambda interpreted-function ,real-lambda-list
         (declare (optimize sb!c::store-closure-debug-pointer))
         (if *dump-info*
             (case *dump-info*
               (:source-path
                ,current-path%)
               (:source-location
                ,source-loc%)
               (:doc
                ,doc%)
               (:set-doc
                (setq ,doc% *set-info*))
               (:lambda-list
                ,lambda-list%)
               (:set-lambda-list
                (setq ,lambda-list% *set-info*))
               (:name
                ,name%)
               (:set-name
                (setq ,name% *set-info*)))
             (progn ,@body))))))

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
