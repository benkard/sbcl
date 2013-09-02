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
(define-symbol-macro go-tag-index-mapping nil)
(define-symbol-macro go-tag-catch-tag-mapping nil)

(defmacro %go (tag &environment env)
  `(throw ',(cdr (assoc tag (macroexpand 'go-tag-catch-tag-mapping env)
                        :test 'eq))
     ,(cdr (assoc tag (macroexpand 'go-tag-index-mapping env)
                  :test 'eq))))

(defmacro %parsed-tagbody (&body body &environment env)
  (let* ((catch-tag (gensym "TAGBODY-CATCH-TAG"))
         (labels-and-bodies (parse-tagbody-tags-and-bodies body))
         (tagbody-labels (mapcar 'first labels-and-bodies))
         (tagbody-blocks (mapcar 'rest labels-and-bodies)))
    `(symbol-macrolet ((go-tag-catch-tag-mapping
                         ,(append (loop for label in tagbody-labels
                                        collect `(,label . ,catch-tag))
                                  (macroexpand 'go-tag-catch-tag-mapping env)))
                       (go-tag-index-mapping
                         ,(append (loop for label in tagbody-labels
                                        for i from 0
                                        collect `(,label . ,i))
                                  (macroexpand 'go-tag-index-mapping env))))
       (%tagbody (,catch-tag)
         ,@tagbody-blocks))))
