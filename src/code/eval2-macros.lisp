(in-package #+sbcl "SB!EVAL2" #-sbcl "SB-EVAL2")


(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +stack-max+ 8))

(defmacro with-environment (env &body body)
  `(call-with-environment ,env (lambda () ,@body)))

(defmacro with-dynamic-extent-environment ((var debug-record parent size) &body body)
  (let ((data% (gensym))
        (size% (gensym)))
    `(let* ((,size% ,size)
            (,data% (make-array (list ,size%)))
            (,var (%make-environment :debug-record ,debug-record :parent ,parent :data ,data%)))
       (declare (type (mod #.(1+ +stack-max+)) ,size%)
                ;; we must not allocate environment objects on the
                ;; stack unless we can be sure that all child
                ;; environments will also be allocated on the stack,
                ;; but we can't really know that.
                (dynamic-extent ,var)
                (dynamic-extent ,data%))
       ,@body)))

(defmacro with-indefinite-extent-environment ((var debug-record parent size) &body body)
  (let ((data% (gensym))
        (size% (gensym)))
    `(let* ((,size% ,size)
            (,data% (make-array (list ,size%)))
            (,var (%make-environment :debug-record ,debug-record :parent ,parent :data ,data%)))
       ,@body)))

(defmacro with-parsed-body ((forms-var specials-var) exprs &body body)
  (let ((decls (gensym)))
    `(multiple-value-bind (,decls ,forms-var) (body-decls&forms ,exprs)
       (let ((,specials-var (mapcan #'decl-specials ,decls)))
         ,@body))))

(defmacro with-context (context &body body)
  `(let ((*context* ,context))
     ,@body))

(defmacro specialize (var value possible-values &body body)
  `(ecase ,value
     ,@(loop for x in (cl:eval possible-values)
             collect
                `((,x) ,(cl:eval `(let ((,var ,x)) ,@body))))))


(defmacro incff (x &optional (num 1))
  (let ((old-x (gensym)))
    `(let ((,old-x ,x))
       (incf ,x ,num)
       ,old-x)))

(defmacro nlet (loop-var bindings &body body)
  `(labels ((,loop-var ,(mapcar #'first bindings)
              ,@body))
     (,loop-var ,@(mapcar #'second bindings))))

(defmacro dnlet (loop-var bindings &body body)
  `(labels ((,loop-var ,(mapcar #'first bindings)
              ,@body))
     (declare (dynamic-extent #',loop-var))
     (,loop-var ,@(mapcar #'second bindings))))
