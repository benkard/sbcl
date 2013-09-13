(in-package "SB!EVAL2")

;; These definitions of BLOCK/RETURN-FROM/RETURN and TAGBODY/GO have
;; been taken from Toilet Lisp.

;; ----
(define-symbol-macro block-mapping nil)

(defmacro %block (block-name &body body &environment env)
  ;; At compile-time, we establish a mapping from block names to
  ;; catch-tags.  A RETURN-FROM is simply translated into a THROW to
  ;; the corresponding tag.
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
(defvar *go-tag-index-mapping* nil)
(defvar *go-tag-catch-tag-mapping* nil)

(defmacro %go (tag)
  (declare (ignore tag))
  (error "GO outside of TAGBODY"))

(defmacro %parsed-tagbody (&body body)
  ;; We wrap each TAGBODY in a CATCH form.  Since TAGBODYs can be
  ;; nested, we track a mapping from TAGBODY labels to their
  ;; corresponding catch-tags.
  ;;
  ;; A GO form is translated into a THROW to the appropriate
  ;; catch-tag.  The value thrown is the index of the tagbody block we
  ;; want to jump to.
  ;;
  ;; The implementation of %TAGBODY handles the actual looping and
  ;; jumping.
  (let* ((catch-tag (gensym "TAGBODY-CATCH-TAG"))
         (labels-and-bodies (parse-tagbody-tags-and-bodies body))
         (tagbody-labels (mapcar 'first labels-and-bodies))
         (tagbody-blocks (mapcar 'rest labels-and-bodies)))
    `(compiler-let ((*go-tag-catch-tag-mapping*
                      (append ',(loop for label in tagbody-labels
                                      collect `(,label . ,catch-tag))
                              *go-tag-catch-tag-mapping*))
                    (*go-tag-index-mapping*
                      (append ',(loop for label in tagbody-labels
                                      for i from 0
                                      collect `(,label . ,i))
                              *go-tag-index-mapping*)))
       (macrolet ((%go (tag)
                    `(throw ',(cdr (assoc tag *go-tag-catch-tag-mapping* :test 'eql))
                       ,(cdr (assoc tag *go-tag-index-mapping* :test 'eql)))))
         (%tagbody (,catch-tag)
           ,@tagbody-blocks)))))
