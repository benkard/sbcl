(in-package "SB-EVAL2")

(setf (find-class 'simple-program-error)
      (find-class 'ccl::simple-program-error))


(defmacro eval-lambda (lambda-list &body body)
  `(ccl:nfunction eval-closure (lambda ,lambda-list ,@body)))

(defmacro interpreted-lambda ((name current-path source-info) lambda-list &body body)
  (declare (ignore current-path source-info))
  `(let ((fn (lambda ,lambda-list ,@body)))
     (if name
         (ccl::lfun-name fn ',name)
         (ccl::lfun-name fn 'interpreted-function))
     fn))

(defun context->native-environment (context)
  (let ((env (ccl::new-lexical-environment))
        (macros
          (loop for (name . expander) in (context-collect context 'context-macros)
                collect `(,name ,expander)))
        (symbol-macros
          (loop for (name . form) in (context-collect context 'context-symbol-macros)
                collect `(,name ,form))))
    (ccl::augment-environment
     env
     :function (mapcan (lambda (lexical)
                         (when (and (listp (lexical-name lexical))
                                    (eq 'function (first (lexical-name lexical))))
                           (list (second (lexical-name lexical)))))
                       (context-collect context 'context-lexicals))
     :variable (mapcan (lambda (lexical)
                         (unless (and (listp (lexical-name lexical))
                                      (eq 'function (first (lexical-name lexical))))
                           (list (lexical-name lexical))))
                       (context-collect context 'context-lexicals))
     :macro macros
     :symbol-macro symbol-macros
     ;;:declare ...
     )
    env))

(defun globally-special-p (var)
  (ccl:proclaimed-special-p var))

(defun globally-constant-p (var)
  (constantp var))