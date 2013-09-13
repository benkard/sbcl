(in-package "SB!EVAL2")

(defclass minimally-compiled-function (c2mop:funcallable-standard-object)
  ((name          :accessor minimally-compiled-function-name
                  :initarg :name)
   (lambda-list   :accessor minimally-compiled-function-lambda-list
                  :initarg :lambda-list)
   (documentation :accessor minimally-compiled-function-documentation
                  :initarg :documentation))
  (:metaclass c2mop:funcallable-standard-class))

(defun make-minimally-compiled-function
    (name lambda-list documentation function)
  (let ((mincfun (make-instance 'minimally-compiled-function
                  :name name
                  :lambda-list lambda-list
                  :documentation documentation)))
    (c2mop:set-funcallable-instance-function mincfun function)
    mincfun))

(defun minimally-compiled-function-p (function)
  (typep function 'minimally-compiled-function))

(defmethod print-object ((obj minimally-compiled-function) stream)
  (print-unreadable-object (obj stream
                            :identity (not (minimally-compiled-function-name obj)))
    (format stream "~A ~A" '#:minimally-compiled-function
            (minimally-compiled-function-name obj))))

(defvar *dyn-vars*)
(defvar *dyn-vals*)
(defvar *mode* :execute)
(defvar *context*)
(defvar *args*)
(defvar *arg-count*)
(defvar *env-box*)
