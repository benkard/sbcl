(in-package "SB!EVAL2")

(defmacro declaim-optimizations ()
  `(declaim (optimize (debug 2) (space 2) (speed 2) (safety 0) (compilation-speed 0))))


(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *impl-compiler-let-syms* '())
  (defvar *impl-named-lambda-syms* '())
  (defvar *impl-named-function-syms* '())
  (defvar *impl-the-syms* '()))


(defun verify-function-name (thing)
  (declare (ignore thing)))


(defmacro eval-lambda ((&optional kind current-path source-loc) &body body)
  (declare (ignore kind current-path source-loc))
  `(lambda () ,@body))

(defmacro interpreted-lambda ((name current-path source-info lambda-list doc)
                              &body body)
  (declare (ignore current-path source-info))
  `(make-minimally-compiled-function ,name
                                     ,lambda-list
                                     ,doc
                                     (lambda (&rest *args*)
                                       (let ((*arg-count* (length *args*)))
                                         ,@body))))

(declaim (inline get-arg))
(defun get-arg (i)
  (elt *args* i))

(declaim (inline get-arglist))
(defun get-arglist ()
  *args*)

(defun current-path ()
  nil)

(defun current-location ()
  nil)

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
       (let (,@(if env?
                     `((,env? ,env))
                     `()))
         (,@(if whole? `(destructuring-bind (&rest ,whole?) ,whole) `(progn))
           (destructuring-bind ,lambda-list (rest ,whole)
             ,@body))))))

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
  (declare (ignore context))
  (error "NYI"))
(defun globally-special-p (var)
  (declare (ignore var))
  (error "NYI"))
(defun globally-constant-p (var)
  (constantp var))
(defun symbol-macro-p (var)
  (not (eq (macroexpand var) var)))

(defun find-fdefn (function-name)
  'function-name)
(defun fdefn-fun (fdefn)
  (fdefinition fdefn))

(defun compile-form (form
                     &optional (mode      *mode*)
                     &aux      (*mode*    :execute))
  (%compile-form form mode))

(defun prepare-form (form)
  (%prepare-form form))
