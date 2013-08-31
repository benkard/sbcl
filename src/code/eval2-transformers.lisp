(in-package #+sbcl "SB!EVAL2" #-sbcl "SB-EVAL2")

;; These definitions of BLOCK/RETURN-FROM/RETURN and TAGBODY/GO have
;; been taken from Toilet Lisp.

;; ----
(define-symbol-macro block-mapping nil)

(defmacro %block (block-name &body body &environment env)
  (let ((catch-tag (gensym)))
    `(symbol-macrolet ((block-mapping
                         ,(acons block-name
                                 catch-tag
                                 (macroexpand 'block-mapping env))))
       (catch ',catch-tag
         ,@body))))

(defmacro %return-from (block-name &optional value &environment env)
  `(throw ',(cdr (assoc block-name (macroexpand 'block-mapping env)
                        :test 'eq))
     ,value))

(defmacro %return (&optional value)
  `(%return-from nil ,value))


;; ----
(define-symbol-macro go-tag-function-mapping nil)
(define-symbol-macro go-tag-catch-tag-mapping nil)

(defmacro %loop (&body forms)
  `(loop ,@forms))

(defmacro %go (tag &environment env)
  `(throw ',(cdr (assoc tag (macroexpand 'go-tag-catch-tag-mapping env)
                        :test 'eq))
     (function ,(cdr (assoc tag (macroexpand 'go-tag-function-mapping env)
                            :test 'eq)))))

(defmacro %tagbody (&body body &environment env)
  (let* ((catch-tag (gensym "TAGBODY-CATCH-TAG"))
         (block-name (gensym "TAGBODY-BLOCK-NAME"))
         (return-value-sym (gensym "TAGBODY-RETURN-VALUE"))
         (end-marker (gensym "TAGBODY-END"))
         (labels-and-bodies (parse-tagbody-tags-and-bodies body))
         (labels-and-catch-tags
           (mapcar (lambda (l&b) (cons (first l&b) catch-tag))
                   labels-and-bodies))
         (labels-and-functions
           (mapcar (lambda (l&b) (cons (first l&b) (gensym "TAGBODY-SECTION")))
                   labels-and-bodies))
         (sections
           (loop with functions = (mapcar #'cdr labels-and-functions)
                 for (label . body) in labels-and-bodies
                 for next-throw in (append (mapcar #'(lambda (fn) `(function ,fn))
                                                   (rest functions))
                                           (list `(quote ,end-marker)))
                 for function-name in (mapcar #'cdr labels-and-functions)
                 collect `(,function-name ()
                            ,@body
                            ,next-throw))))
    `(symbol-macrolet ((go-tag-catch-tag-mapping
                         ,(append labels-and-catch-tags
                                  (macroexpand 'go-tag-catch-tag-mapping env)))
                       (go-tag-function-mapping
                         ,(append labels-and-functions
                                  (macroexpand 'go-tag-function-mapping env))))
       (labels (,@sections)
         (%block ,block-name
           (let (,return-value-sym)
             (%loop
               (setq ,return-value-sym
                     (catch ',catch-tag
                       (if ,return-value-sym
                           (funcall ,return-value-sym)
                           (,(cdar labels-and-functions)))))
               (when (eq ,return-value-sym ',end-marker)
                 (%return-from ,block-name nil)))))))))
