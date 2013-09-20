(in-package "SB!EVAL2")

(declaim (optimize (debug 0) (space 0) (speed 3) (safety 0) (compilation-speed 0)))


;;;; EVAL-CLOSUREs
;;;
;;; An eval-closure is a function corresponding to a compiled form
;;; which, when evaluated, acts as if interpreting the form in the
;;; supplied environment, and returns the result.
(deftype eval-closure () `(function (environment) *))


;;;; DEBUG RECORDS
;;;
;;; Debug records store information interesting to the debugger.  They
;;; are linked from environments, which can be accessed by the
;;; debugger through various means (in the case of SBCL, this is
;;; primarily through access through the DEBUG-VAR corresponding to
;;; the first argument of the EVAL-CLOSURE.)
(defstruct (debug-record (:constructor
                             make-debug-record
                             (context &optional (lambda-list :none) function-name))
                         #+(or)   ;uncomment this if you want to make
                                  ;VM code more human-readable for
                                  ;debugging purposes
                         (:print-function (lambda (object stream foo)
                                            (declare (ignore object foo))
                                            (format stream "#<DEBUG-RECORD>"))))
  (context nil :type context)
  (lambda-list nil :type (or list (member :none)))
  (function-name nil))


;;;; ENVIRONMENTS
;;;
;;; Environments are the things that evaluated code passes around at
;;; runtime to track variable bindings.  The design is a conventional
;;; linked style where every environment has a link to its parent
;;; environment.  In order to access a binding in an ancestral
;;; environment, the chain of environments must be traversed.
;;; Variables are represented as cells in a SIMPLE-VECTOR.  The
;;; information mapping variable names to vector cells/parent hop
;;; counts is compile-time-only (see the CONTEXT structure below),
;;; since the compiler translates variable accesses into instructions
;;; of the form (%envref <hopcount> <vector-index>).
(declaim (inline %make-environment
                 environment-debug-record
                 environment-parent
                 environment-data))
(defstruct (environment (:constructor
                            %make-environment
                            (debug-record parent data)))
  (debug-record nil :type (or null debug-record))
  (parent nil :type (or null environment))
  (data nil :type simple-vector))

(declaim (inline make-null-environment))
(defun make-null-environment ()
  (make-environment (make-debug-record (make-null-context)) nil 0))

(declaim (inline make-environment))
(defun make-environment (debug-record
                         parent
                         &optional (size 0)
                         &aux (data
                               (if (zerop (the fixnum size))
                                   #()
                                   (make-array (list size)))))
  (%make-environment debug-record parent data))

(declaim (inline call-with-environment))
(declaim (ftype (function (environment function) *) call-with-environment))
(defun call-with-environment (env thunk)
  (funcall thunk env))

;;; ENVIRONMENT accessors
(declaim (inline environment-value))
(defun environment-value (env nesting offset)
  (dotimes (i (the fixnum nesting))
    (setq env (environment-parent env)))
  (svref (environment-data env) offset))

(declaim (inline (setf environment-value)))
(defun (setf environment-value) (val env nesting offset)
  (dotimes (i (the fixnum nesting))
    (setq env (environment-parent env)))
  (setf (svref (environment-data env) offset) val))


;;;; CONTEXTS
;;;
;;; A LEXICAL is a compile-time record containing information on how
;;; to access the variable named by a given NAME.
(defstruct lexical
  (name    nil :type (or symbol list))
  (offset  nil :type fixnum)
  (nesting nil :type fixnum))

(defun make-env-lexical (name offset &optional (nesting -1))
  (make-lexical :name name :offset offset :nesting nesting))

(defun lexical-with-nesting (lexical nesting)
  (make-lexical :name (lexical-name lexical) :offset (lexical-offset lexical) :nesting nesting))

(declaim (ftype (function (context function) *) call-with-context))
(defun call-with-context (context thunk)
  (let ((*context* context))
    (declare (special *context*))
    (funcall thunk)))


;;; The CONTEXT structure contains all information tracked by the
;;; compiler during syntactical analysis.  Contexts are built up at
;;; compile-time as environments are built up at runtime.  They are
;;; also linked hierarchically, so the compiler needs to hop through
;;; the ancestor chain to collect all variables/go-labels/catch-tags,
;;; etc.
;;;
;;; Note: We treat local functions as variables with a name of
;;; `(FUNCTION ,function-name).  (In theory, this can be used to
;;; dynamically bind local functions.)
(defstruct (context (:constructor make-context (&optional parent)))
  ;; The parent context.  All information in the parent context is
  ;; also relevant for this context except for things that are
  ;; overridden by new information.
  parent
  ;; Does this context correspond to a new ENVIRONMENT being created
  ;; at runtime?  If so, this means runtime code needs to hop one
  ;; level farther than before to access existing variable bindings.
  (env-hop nil :type boolean)
  ;; A list of (NAME . FORM) pairs.
  (symbol-macros nil :type list)
  ;; A list of (NAME . FUNCTION) pairs.
  (macros nil :type list)
  ;; A list of LEXICALs corresponding to the variables newly bound in
  ;; this context.  If this is non-null, ENV-HOP must be true.
  (lexicals nil :type list)
  ;; A list of variables locally declared SPECIAL in this context.
  (specials nil :type list)
  ;; The environment for COMPILER-LET, accessible from locally defined
  ;; macros.
  (%evaluation-environment nil :type (or null environment))
  ;; The context corresponding to the %EVALUATION-ENVIRONMENT, used
  ;; for compiling locally defined macros.
  (%evaluation-context nil :type (or null context)))

(defun make-null-context ()
  (make-context nil))

(defun make-lexical-context (context)
  (let ((new-context (make-context context)))
    (setf (context-env-hop new-context) t)
    new-context))


;;;; CONTEXT accessors
;;;
;;; Most of the functions that augment a context return a new context
;;; with the existing one as the parent.  Exceptions are marked with a
;;; ! in the name (such as CONTEXT-ADD-SPECIAL!).

;;; Evaluation environment
(defun context-evaluation-environment (context)
  (let ((parent (context-parent context)))
    (or (context-%evaluation-environment context)
        (and parent (context-evaluation-environment parent))
        (make-null-environment))))

(defun context-add-evaluation-bindings (context bindings)
  (let* ((new-context (make-context context))
         (evlctx (context-evaluation-context context))
         (evlenv (make-environment nil
                                   (context-evaluation-environment context)
                                   (length bindings))))
    (loop for value in (mapcar #'cdr bindings)
          for i from 0
          do (setf (environment-value evlenv 0 i) value))
    (setf (context-%evaluation-environment new-context)
          evlenv)
    (setf (context-%evaluation-context new-context)
          (context-add-env-lexicals evlctx (mapcar #'car bindings)))
    new-context))

(defun context-evaluation-context (context)
  (let ((parent (context-parent context)))
    (or (context-%evaluation-context context)
        (and parent (context-evaluation-context parent))
        (make-null-context))))


;;; Macros and symbol macros
(defun context-find-symbol-macro (context symmac)
  "If a symbol macro called SYMMAC exists in CONTEXT, return a singleton list of its expansion, otherwise return NIL."
  (let ((parent (context-parent context)))
    (and (not (member symmac
                      (context-lexicals context)
                      :test #'equal
                      :key #'lexical-name))
         (not (member symmac (context-specials context) :test #'equal))
         (or (let ((record? (assoc (the symbol symmac) (context-symbol-macros context))))
               (and record? (list (cdr record?))))
             (and parent (context-find-symbol-macro parent symmac))))))

(defun context-find-macro (context mac)
  "If a macro called MAC exists in CONTEXT, return a singleton list of its expander function, otherwise return NIL."
  (let ((parent (context-parent context)))
    (and (not (member `(function ,mac)
                      (context-lexicals context)
                      :test #'equal
                      :key #'lexical-name))
         (or (cdr (assoc (the (or symbol list) mac)
                         (context-macros context)
                         :test #'equal))
             (and parent (context-find-macro parent mac))))))

(defun context-add-symbol-macros (context bindings)
  (let ((new-context (make-context context)))
    (setf (context-symbol-macros new-context)
          (append bindings (context-symbol-macros new-context)))
    new-context))

(defun context-add-macros (context bindings)
  (let ((new-context (make-context context)))
    (setf (context-macros new-context)
          (append bindings (context-macros new-context)))
    new-context))


;;; Lexical information
(defun context-var-symbol-macro-p (context var)
  (and (not (find var (context-specials context) :test #'equal))
       (not (find var (context-lexicals context) :key #'lexical-name :test #'equal))
       (or (find var (context-symbol-macros context) :key #'car :test #'equal)
           (and (context-parent context)
                (context-var-symbol-macro-p (context-parent context) var)))))

(defun context-var-lexical-p (context var)
  (and (not (find var (context-specials context) :test #'equal))
       (not (find var (context-symbol-macros context) :key #'car :test #'equal))
       (or (find var (context-lexicals context) :key #'lexical-name :test #'equal)
           (and (context-parent context)
                (context-var-lexical-p (context-parent context) var)))))

(defun context-var-special-p (context var)
  (and (not (find var (context-lexicals context) :key #'lexical-name :test #'equal))
       (not (find var (context-symbol-macros context) :key #'car :test #'equal))
       (or (find var (context-specials context) :test #'equal)
           (and (context-parent context)
                (context-var-special-p (context-parent context) var)))))

(declaim (ftype (function (context (or symbol list)) *) local-function-p))
(defun local-function-p (context f)
  (context-find-function context f))


;;; Lexical and special variables
(defun context-add-env-lexicals (context vars)
  ;; Open a new variable context, set env-hop to true.
  (let ((new-context (make-context context)))
    (setf (context-env-hop new-context) t)
    (setf (context-lexicals new-context)
          (loop for i fixnum from 0
                for v in vars
                collect (make-env-lexical v i)))
    new-context))

(defun context-add-env-lexical! (context var)
  (push (make-env-lexical var (length (context-lexicals context)))
        (context-lexicals context))
  (values))

(defun context-add-specials (context vars)
  (let ((new-context (make-context context)))
    (setf (context-specials new-context) vars)
    new-context))

(defun context-add-special! (context var)
  (push var (context-specials context))
  (values))

(defun context-add-env-functions (context fs)
  (context-add-env-lexicals context (mapcar (lambda (x) `(function ,x)) fs)))


(defun context-find-lexical (context var)
  (find var (context-collect-lexicals context) :key #'lexical-name :test #'equal))

(declaim (ftype (function (context (or symbol list)) *) context-find-function))
(defun context-find-function (context f)
  (context-find-lexical context `(function ,f)))


;;; Utilities
(defun context-collect (context f)
  "Walk the ancestor chain of CONTEXT and return all F of the contexts, appended together.

This is effectively a MAPCAN on the ancestor chain of CONTEXT."
  (let ((parent (context-parent context)))
    (append (funcall f context) (and parent (context-collect parent f)))))

(defun context-collect-lexicals (context)
  "Find all LEXICALs bound in CONTEXT and all of its ancestors."
  ;; In order to make the returned information correct, we need to
  ;; augment the LEXICALs with the appropriate nesting/environment hop
  ;; count.  We do this by incrementing a counter each time we
  ;; encounter a context corresponding to a lexical environment,
  ;; indicated by the ENV-HOP flag.
  (loop with env-level = 0
        until (null context)
        for records = (context-lexicals context)
        nconc (mapcar #'(lambda (record) (lexical-with-nesting record env-level))
                      records)
        when (context-env-hop context)
        do (incf env-level)
        do (setq context (context-parent context))))
