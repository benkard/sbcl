;;#!+sbcl
;;(in-package "SB!EVAL2")
;;#!-sbcl
(in-package "SB-EVAL2")

(defmacro eval-lambda ((&optional kind current-path source-loc) &body body)
  `(lambda () ,@body))

(defmacro interpreted-lambda ((name current-path source-info) lambda-list &body body)
  (declare (ignore name current-path source-info))
  `(lambda ,lambda-list ,@body))

(defun self-evaluating-p (form)
  (or (keywordp form)
      (not (or (symbolp form) (consp form)))))

(defun fun-name-block-name (fun-name)
  (etypecase fun-name
    (symbol fun-name)
    (cons   (second fun-name))))

(defun parse-macrolet-binding-form (lambda-list whole body name env)
  (let* (;;(envtail (member '&environment lambda-list))
         (envpos (position '&environment lambda-list))
         ;;(env-var (second envtail))
         whole?
         env?)
    (when envpos
      (psetq env?        (elt lambda-list (1+ envpos))
             lambda-list (append (subseq lambda-list 0 envpos)
                                 (subseq lambda-list (+ envpos 2)))))
    (when (eq (first lambda-list) '&whole)
      (psetq whole?      (second lambda-list)
             lambda-list (cddr lambda-list)))
    `(block ,(fun-name-block-name name)
       (destructuring-bind ,lambda-list ,whole
         (let (,@(if env?
                     `((,env? ,env))
                     `())
               ,@(if whole?
                     `((,whole? ,whole))
                     `()))
           ,@body)))))

(defun parse-lambda-list (lambda-list)
  ;; returns values:
  ;;
  ;;   (required optional restp rest keyp keys allowp auxp aux)
  ;;
  (multiple-value-bind (required optional rest? keys allowp aux keyp)
      (alexandria::parse-ordinary-lambda-list lambda-list
                                              :normalize nil
                                              :allow-specializers nil)
    (values required optional rest? rest? keyp keys allowp aux aux)))

(defun context->native-environment (context)
  (error "NYI"))
(defun globally-special-p (var)
  (error "NYI"))
(defun globally-constant-p (var)
  (constantp var))

