(in-package "SB!EVAL2")

(define-condition simple-program-error (ccl::simple-program-error)
  ())

(eval-when (:compile-toplevel :load-toplevel :execute)
  (pushnew 'ccl:compiler-let *impl-compiler-lets*)
  (pushnew 'ccl:nfunction *impl-named-function-syms*))


(defun verify-function-name (thing)
  (assert (ccl::valid-function-name-p thing)))

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
               (let ((*arg-count* (length *args*)))
                 ,@body))))
     (if name
         (ccl::lfun-name fn ,name)
         (ccl::lfun-name fn 'minimally-compiled-function))
     (let* ((mincfun (make-minimally-compiled-function ,name
                                                       ,lambda-list
                                                       ,doc
                                                       fn))
            (bits (ccl::lfun-bits mincfun)))
       (ccl::lfun-bits mincfun (logior bits (ash 1 ccl::$lfbits-nonnullenv-bit)))
       mincfun)))

(defun context->native-environment (context)
  (etypecase context
    (null
     (ccl::new-lexical-environment))
    (context
     (let ((env
             (context->native-environment (context-parent context)))
           (macros
             (loop for (name . expander) in (context-macros context)
                   collect `(,name ,expander)))
           (symbol-macros
             (loop for (name . form) in (context-symbol-macros context)
                   collect `(,name ,form)))
           (functions
             (mapcan (lambda (lexical)
                       (when (and (listp (lexical-name lexical))
                                  (eq 'function (first (lexical-name lexical))))
                         (list (second (lexical-name lexical)))))
                     (context-lexicals context)))
           (variables
             (mapcan (lambda (lexical)
                       (unless (and (listp (lexical-name lexical))
                                    (eq 'function (first (lexical-name lexical))))
                         (list (lexical-name lexical))))
                     (context-lexicals context))))
       (ccl::augment-environment
        env
        :function functions
        :variable variables
        :macro macros
        :symbol-macro symbol-macros
        ;;:declare ...
        )))))

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
