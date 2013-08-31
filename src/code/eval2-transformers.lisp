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

(defmacro %go (tag &environment env)
  `(throw ',(cdr (assoc tag (macroexpand 'go-tag-catch-tag-mapping env)
                        :test 'eq))
     (function ,(cdr (assoc tag (macroexpand 'go-tag-function-mapping env)
                            :test 'eq)))))

(defmacro %tagbody (&body body &environment env)
  (let* (labels-and-catch-tags
         labels-and-functions
         (catch-tag (gensym "TAGBODY-CATCH-TAG"))
         (block-name (gensym "TAGBODY-BLOCK-NAME"))
         (return-value-sym (gensym "TAGBODY-RETURN-VALUE"))
         (end-marker (gensym "TAGBODY-END"))
         (sections
          (mapcon (let (current-label
                        accumulated-clauses
                        current-function)
                    (lambda (clause-and-rest)
                      (let ((clause (car clause-and-rest))
                            (rest (cdr clause-and-rest)))
                        (cond
                          ((atom clause)
                           (when current-function
                             (push (cons current-label current-function)
                                    labels-and-functions)
                             (push (cons current-label catch-tag)
                                    labels-and-catch-tags))
                           (let ((old-function current-function))
                             (setq current-label clause
                                   current-function (gensym "TAGBODY-SECTION"))
                             (prog1
                               `((,old-function ()
                                   ;; Yes, we generate this even when
                                   ;; OLD-FUNCTION is NIL.  In this
                                   ;; case, though, the LABELS form
                                   ;; never sees the definition.  Grep
                                   ;; for (cddr (first sections)) below
                                   ;; in order to see how we make use of
                                   ;; the generated lambda form instead.
                                   ,@(nreverse accumulated-clauses)
                                   #',current-function)
                                 ,@(when (endp rest)
                                     `((,current-function ()
                                                          ',end-marker))))
                               (setq accumulated-clauses nil))))
                          (t (push clause accumulated-clauses)
                             (if (endp rest)
                                 (progn
                                   (when current-function
                                     (push (cons current-label current-function)
                                           labels-and-functions)
                                     (push (cons current-label catch-tag)
                                           labels-and-catch-tags))
                                   `((,current-function ()
                                        ,@(nreverse accumulated-clauses)
                                        ',end-marker)))
                                 nil))))))
                   body)))
    `(symbol-macrolet ((go-tag-catch-tag-mapping
                         ,(append labels-and-catch-tags
                                  (macroexpand 'go-tag-catch-tag-mapping env)))
                       (go-tag-function-mapping
                         ,(append labels-and-functions
                                  (macroexpand 'go-tag-function-mapping env))))
       (labels (,@(rest sections))
         (%block ,block-name
           (let (,return-value-sym)
             (%loop
               (setq ,return-value-sym
                     (catch ',catch-tag
                       (if ,return-value-sym
                           (funcall ,return-value-sym)
                           (progn ,@(cddr (first sections))))))
               (when (eq ,return-value-sym ',end-marker)
                 (%return-from ,block-name nil)))))))))
