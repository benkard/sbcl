(in-package "SB!EVAL2")

(define-condition simple-program-error (ccl::simple-program-error)
  ())

#+(or)
(setf (find-class 'simple-program-error)
      (find-class 'ccl::simple-program-error))


(defmacro eval-lambda (lambda-list (&optional kind current-path source-loc) &body body)
  (declare (ignore current-path source-loc))
  `(ccl:nfunction ,(if kind
                       `(eval-closure ,kind)
                       'eval-closure)
                  (lambda ,lambda-list ,@body)))

(defmacro interpreted-lambda ((name current-path source-info lambda-list doc)
                              &body body)
  (declare (ignore current-path source-info))
  `(let ((fn (lambda (&rest *args*)
               (let ((*argnum* (length *args*)))
                 ,@body))))
     (if name
         (ccl::lfun-name fn ,name)
         (ccl::lfun-name fn 'minimally-compiled-function))
     (make-minimally-compiled-function ,name
                                       ,lambda-list
                                       ,doc
                                       fn)))

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
     )))

(defun globally-special-p (var)
  (ccl:proclaimed-special-p var))

(defun globally-constant-p (var)
  (ccl:constant-symbol-p var))

(defun symbol-macro-p (var)
  (not (eq (macroexpand var) var)))

(declaim (inline find-fdefn))
(defun find-fdefn (function-name)
  (ccl::symptr->symvector
   (ccl::%symbol->symptr
    (ccl::validate-function-name function-name))))

(declaim (inline fdefn-fun))
(defun fdefn-fun (fdefn)
  (let ((fun (ccl::%svref fdefn target::symbol.fcell-cell)))
    (when (not (eq fun ccl::%unbound-function%))
      fun)))
