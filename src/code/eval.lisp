;;;; EVAL and friends

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!IMPL")

(defparameter *eval-calls* 0)

(defun !eval-cold-init ()
  (setf *eval-calls* 0
        *evaluator-mode* :compile)
  #!+sb-eval
  (setf sb!eval::*eval-level* -1
        sb!eval::*eval-verbose* nil))

(defvar *eval-source-context* nil)

(defvar *eval-tlf-index* nil)
(defvar *eval-source-info* nil)

;;;; Turns EXPR into a lambda-form we can pass to COMPILE. Returns
;;;; a secondary value of T if we must call the resulting function
;;;; to evaluate EXPR -- if EXPR is already a lambda form, there's
;;;; no need.
(defun make-eval-lambda (expr)
  (if (typep expr `(cons (member lambda named-lambda lambda-with-lexenv)))
      (values expr nil)
      (values `(lambda ()
                 ;; why PROGN? So that attempts to eval free declarations
                 ;; signal errors rather than return NIL. -- CSR, 2007-05-01
                 (progn ,expr))
              t)))

;;; general case of EVAL (except in that it can't handle toplevel
;;; EVAL-WHEN magic properly): Delegate to #'COMPILE.
(defun %simple-eval (expr lexenv)
  (multiple-value-bind (lambda call) (make-eval-lambda expr)
    (let ((fun
            ;; This tells the compiler where the lambda comes from, in case it
            ;; wants to report any problems.
            (let ((sb!c::*source-form-context-alist*
                    (acons lambda *eval-source-context*
                           sb!c::*source-form-context-alist*)))
              (handler-bind (;; Compiler notes just clutter up the REPL:
                             ;; anyone caring about performance should not
                             ;; be using EVAL.
                             (compiler-note #'muffle-warning))
                (sb!c:compile-in-lexenv
                 nil lambda lexenv *eval-source-info* *eval-tlf-index* (not call))))))
      (declare (function fun))
      (if call
          (funcall fun)
          fun))))

;;; Handle PROGN and implicit PROGN.
(defun simple-eval-progn-body (progn-body lexenv)
  (unless (list-with-length-p progn-body)
    (let ((*print-circle* t))
      (error 'simple-program-error
             :format-control
             "~@<not a proper list in PROGN or implicit PROGN: ~2I~_~S~:>"
             :format-arguments (list progn-body))))
  ;; Note:
  ;;   * We can't just use (MAP NIL #'EVAL PROGN-BODY) here, because we
  ;;     need to take care to return all the values of the final EVAL.
  ;;   * It's left as an exercise to the reader to verify that this
  ;;     gives the right result when PROGN-BODY is NIL, because
  ;;     (FIRST NIL) = (REST NIL) = NIL.
  (do* ((i progn-body rest-i)
        (rest-i (rest i) (rest i)))
      (nil)
    (if rest-i ; if not last element of list
        (simple-eval-in-lexenv (first i) lexenv)
        (return (simple-eval-in-lexenv (first i) lexenv)))))

(defun simple-eval-locally (exp lexenv &key vars)
  (multiple-value-bind (body decls)
      (parse-body (rest exp) :doc-string-allowed nil)
    (let ((lexenv
           ;; KLUDGE: Uh, yeah.  I'm not anticipating
           ;; winning any prizes for this code, which was
           ;; written on a "let's get it to work" basis.
           ;; These seem to be the variables that need
           ;; bindings for PROCESS-DECLS to work
           ;; (*FREE-FUNS* and *FREE-VARS* so that
           ;; references to free functions and variables
           ;; in the declarations can be noted;
           ;; *UNDEFINED-WARNINGS* so that warnings about
           ;; undefined things can be accumulated [and
           ;; then thrown away, as it happens]). -- CSR,
           ;; 2002-10-24
           (let* ((sb!c:*lexenv* lexenv)
                  (sb!c::*free-funs* (make-hash-table :test 'equal))
                  (sb!c::*free-vars* (make-hash-table :test 'eq))
                  (sb!c::*undefined-warnings* nil))
             ;; FIXME: VALUES declaration
             (sb!c::process-decls decls
                                  vars
                                  nil
                                  :lexenv lexenv
                                  :context :eval))))
      (simple-eval-progn-body body lexenv))))

;;;; EVAL-ERROR
;;;;
;;;; Analogous to COMPILER-ERROR, but simpler.

(define-condition eval-error (encapsulated-condition)
  ()
  (:report (lambda (condition stream)
             (print-object (encapsulated-condition condition) stream))))

(defun eval-error (condition)
  (signal 'eval-error :condition condition)
  (bug "Unhandled EVAL-ERROR"))

;;; Pick off a few easy cases, and the various top level EVAL-WHEN
;;; magical cases, and call %SIMPLE-EVAL for the rest.
(defun simple-eval-in-lexenv (original-exp lexenv)
  (declare (optimize (safety 1)))
  ;; (aver (lexenv-simple-p lexenv))
  (incf *eval-calls*)
  (sb!c:with-compiler-error-resignalling
    (let ((exp (macroexpand original-exp lexenv)))
      (handler-bind ((eval-error
                       (lambda (condition)
                         (error 'interpreted-program-error
                                :condition (encapsulated-condition condition)
                                :form exp))))
        (typecase exp
          (symbol
           (ecase (info :variable :kind exp)
             ((:special :global :constant :unknown)
              (symbol-value exp))
             ;; FIXME: This special case here is a symptom of non-ANSI
             ;; weirdness in SBCL's ALIEN implementation, which could
             ;; cause problems for e.g. code walkers. It'd probably be
             ;; good to ANSIfy it by making alien variable accessors
             ;; into ordinary forms, e.g. (SB-UNIX:ENV) and (SETF
             ;; SB-UNIX:ENV), instead of magical symbols, e.g. plain
             ;; SB-UNIX:ENV. Then if the old magical-symbol syntax is to
             ;; be retained for compatibility, it can be implemented
             ;; with DEFINE-SYMBOL-MACRO, keeping the code walkers
             ;; happy.
             (:alien
              (sb!alien-internals:alien-value exp))))
          (list
           (let ((name (first exp))
                 (n-args (1- (length exp))))
             (case name
               ((function)
                (unless (= n-args 1)
                  (error "wrong number of args to FUNCTION:~% ~S" exp))
                (let ((name (second exp)))
                  (if (and (legal-fun-name-p name)
                           (not (consp (let ((sb!c:*lexenv* lexenv))
                                         (sb!c:lexenv-find name funs)))))
                      (%coerce-name-to-fun name)
                      ;; FIXME: This is a bit wasteful: it would be nice to call
                      ;; COMPILE-IN-LEXENV with the lambda-form directly, but
                      ;; getting consistent source context and muffling compiler notes
                      ;; is easier this way.
                      (%simple-eval original-exp lexenv))))
               ((quote)
                (unless (= n-args 1)
                  (error "wrong number of args to QUOTE:~% ~S" exp))
                (second exp))
               (setq
                (unless (evenp n-args)
                  (error "odd number of args to SETQ:~% ~S" exp))
                (unless (zerop n-args)
                  (do ((name (cdr exp) (cddr name)))
                      ((null name)
                       (do ((args (cdr exp) (cddr args)))
                           ((null (cddr args))
                            ;; We duplicate the call to SET so that the
                            ;; correct value gets returned.
                            (set (first args)
                                 (simple-eval-in-lexenv (second args) lexenv)))
                         (set (first args)
                              (simple-eval-in-lexenv (second args) lexenv))))
                    (let ((symbol (first name)))
                      (case (info :variable :kind symbol)
                        (:special)
                        (t (return (%simple-eval original-exp lexenv))))
                      (unless (type= (info :variable :type symbol)
                                     *universal-type*)
                        ;; let the compiler deal with type checking
                        (return (%simple-eval original-exp lexenv)))))))
               ((progn)
                (simple-eval-progn-body (rest exp) lexenv))
               ((eval-when)
                ;; FIXME: DESTRUCTURING-BIND returns ARG-COUNT-ERROR
                ;; instead of PROGRAM-ERROR when there's something wrong
                ;; with the syntax here (e.g. missing SITUATIONS). This
                ;; could be fixed by hand-crafting clauses to catch and
                ;; report each possibility, but it would probably be
                ;; cleaner to write a new macro
                ;; DESTRUCTURING-BIND-PROGRAM-SYNTAX which does
                ;; DESTRUCTURING-BIND and promotes any mismatch to
                ;; PROGRAM-ERROR, then to use it here and in (probably
                ;; dozens of) other places where the same problem
                ;; arises.
                (destructuring-bind (eval-when situations &rest body) exp
                  (declare (ignore eval-when))
                  (multiple-value-bind (ct lt e)
                      (sb!c:parse-eval-when-situations situations)
                    ;; CLHS 3.8 - Special Operator EVAL-WHEN: The use of
                    ;; the situation :EXECUTE (or EVAL) controls whether
                    ;; evaluation occurs for other EVAL-WHEN forms; that
                    ;; is, those that are not top level forms, or those
                    ;; in code processed by EVAL or COMPILE. If the
                    ;; :EXECUTE situation is specified in such a form,
                    ;; then the body forms are processed as an implicit
                    ;; PROGN; otherwise, the EVAL-WHEN form returns NIL.
                    (declare (ignore ct lt))
                    (when e
                      (simple-eval-progn-body body lexenv)))))
               ((locally)
                (simple-eval-locally exp lexenv))
               ((macrolet)
                (destructuring-bind (definitions &rest body)
                    (rest exp)
                  (let ((lexenv
                          (let ((sb!c:*lexenv* lexenv))
                            (sb!c::funcall-in-macrolet-lexenv
                             definitions
                             (lambda (&key funs)
                               (declare (ignore funs))
                               sb!c:*lexenv*)
                             :eval))))
                    (simple-eval-locally `(locally ,@body) lexenv))))
               ((symbol-macrolet)
                (destructuring-bind (definitions &rest body) (rest exp)
                  (multiple-value-bind (lexenv vars)
                      (let ((sb!c:*lexenv* lexenv))
                        (sb!c::funcall-in-symbol-macrolet-lexenv
                         definitions
                         (lambda (&key vars)
                           (values sb!c:*lexenv* vars))
                         :eval))
                    (simple-eval-locally `(locally ,@body) lexenv :vars vars))))
               ((if)
                (destructuring-bind (test then &optional else) (rest exp)
                  (eval-in-lexenv (if (eval-in-lexenv test lexenv)
                                      then
                                      else)
                                  lexenv)))
               ((let let*)
                (%simple-eval exp lexenv))
               (t
                (if (and (symbolp name)
                         (eq (info :function :kind name) :function))
                    (collect ((args))
                      (dolist (arg (rest exp))
                        (args (eval-in-lexenv arg lexenv)))
                      (apply (symbol-function name) (args)))
                    (%simple-eval exp lexenv))))))
          (t
           exp))))))

#!+sb-eval
(defun eval-in-lexenv (exp lexenv)
  (ccase sb!ext:*evaluator-mode*
    ((:interpret)
     (sb!eval:eval-in-native-environment exp lexenv))
    ((:minimally-compile)
     (sb!eval2:call-with-environment
      (sb!eval2:make-null-environment)
      (sb!eval2:prepare-form
       (sb!eval2:call-with-context
        (sb!eval2:native-environment->context lexenv)
        (lambda ()
          (sb!eval2:compile-form exp (if *eval-tlf-index*
                                         :execute-tlf
                                         :execute)))))))
    ((:compile)
     (simple-eval-in-lexenv exp lexenv))))

#!-sb-eval
(defun eval-in-lexenv (exp lexenv)
  (simple-eval-in-lexenv exp lexenv))

(defun eval (original-exp)
  #!+sb-doc
  "Evaluate the argument in a null lexical environment, returning the
   result or results."
  (let ((*eval-source-context* original-exp)
        (*eval-tlf-index* nil)
        (*eval-source-info* nil))
    (eval-in-lexenv original-exp (make-null-lexenv))))

(defun eval-tlf (original-exp tlf-index &optional (lexenv (make-null-lexenv)))
  (let ((*eval-source-context* original-exp)
        (*eval-tlf-index* tlf-index)
        (*eval-source-info* sb!c::*source-info*))
    (eval-in-lexenv original-exp lexenv)))

;;; miscellaneous full function definitions of things which are
;;; ordinarily handled magically by the compiler

(defun apply (function arg &rest arguments)
  #!+sb-doc
  "Apply FUNCTION to a list of arguments produced by evaluating ARGUMENTS in
  the manner of LIST*. That is, a list is made of the values of all but the
  last argument, appended to the value of the last argument, which must be a
  list."
  (cond ((atom arguments)
         (apply function arg))
        ((atom (cdr arguments))
         (apply function (cons arg (car arguments))))
        (t (do* ((a1 arguments a2)
                 (a2 (cdr arguments) (cdr a2)))
                ((atom (cdr a2))
                 (rplacd a1 (car a2))
                 (apply function (cons arg arguments)))))))

(defun funcall (function &rest arguments)
  #!+sb-doc
  "Call FUNCTION with the given ARGUMENTS."
  (apply function arguments))

(defun values (&rest values)
  #!+sb-doc
  "Return all arguments, in order, as values."
  (declare (truly-dynamic-extent values))
  (values-list values))

(defun values-list (list)
  #!+sb-doc
  "Return all of the elements of LIST, in order, as values."
  (values-list list))
