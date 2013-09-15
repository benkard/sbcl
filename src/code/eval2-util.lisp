(in-package "SB!EVAL2")


;;;; LAMBDA LIST PARSING FUNCTIONS
;;;
;;; These functions take a non-normalized entry of a regular lambda
;;; list and return whatever information about the entry is requested.
;;; They deal with the various special cases and different forms of
;;; lambda-list entries, such as the ((VAR KEY) DEFAULT SUPPLIEDP)
;;; form of &KEY arguments.
;;;
(defun lambda-binding-vars (entry kind)
  "Return all variables bound by the lambda list entry ENTRY.

KIND must be one of :KEY, :OPTIONAL, :AUX, or :REQUIRED."
  (check-type kind (member :aux :optional :key :required))
  (ecase kind
    ((:key :optional)
     (etypecase entry
       (cons   (list (etypecase (first entry)
                       (cons   (second (first entry)))
                       (symbol (first entry)))
                     (if (cddr entry)
                         (third entry)
                         (gensym))))
       (symbol (list entry (gensym)))))
    ((:required)
     (etypecase entry
       (cons   (list (first entry)))
       (symbol entry)))
    ((:aux)
     (etypecase entry
       (cons   (list (first entry)))
       (symbol entry)))))

(defun lambda-binding-main-var (entry)
  (etypecase entry
    (cons   (etypecase (first entry)
              (cons   (second (first entry)))
              (symbol (first entry))))
    (symbol entry)))

(defun lambda-binding-suppliedp-var (entry)
  (etypecase entry
    (cons (third entry))
    (symbol nil)))

(defun lambda-simple-binding-vars (entry)
  (etypecase entry
    (cons   (list (first entry)))
    (symbol (list entry))))

(defun lambda-binding-default (entry)
  (etypecase entry
    (cons   (second entry))
    (symbol nil)))

(defun lambda-key (entry)
  (flet ((keywordify (sym)
           (intern (symbol-name sym) "KEYWORD")))
    (etypecase entry
      (cons   (etypecase (first entry)
                (cons   (first (first entry)))
                (symbol (keywordify (first entry)))))
      (symbol (keywordify entry)))))


;;;; SOURCE CODE ANALYSIS
(defun maybe-closes-p (context form)
  "Check whether FORM potentially closes over anything not bound in CONTEXT.

We use this to determine whether environments corresponding to
children of CONTEXT can be stack-allocated."
  (declare (ignore context form))
  ;; FIXME
  ;;
  ;; What we really want to do here is macroexpand FORM and have a
  ;; look at whether there are any potential closures there.  It
  ;; should be pretty easy to simply check for the mere presence of
  ;; LAMBDA, SB-INT:NAMED-LAMBDA, FLET, and LABELS.
  ;;
  ;; Beyond that, it's tricky.  We mustn't assume that FORM doesn't
  ;; close over the new enviroment we want to establish just because
  ;; it doesn't close over one of the new environment's direct lexical
  ;; variables.  There could be a child environment it closes over,
  ;; which still means we need to keep the environment on the heap.
  ;;
  ;; Since this function is used for optimization purposes only, it's
  ;; okay to just be conservative and return T here for now.
  t)

(defun body-decls&forms (exprs)
  (let* ((decl-exprs
           (loop while (and (consp (first exprs))
                            (eq 'declare (first (first exprs))))
                 for expr = (pop exprs)
                 collect expr))
         (decls (reduce #'append (mapcar #'rest decl-exprs))))
    (values decls exprs)))

(defun decl-specials (declaration)
  (when (eq (first declaration) 'special)
    (rest declaration)))

(defun parse-tagbody-tags-and-bodies (forms)
  (let ((next-form (gensym))
        (finishp nil))
    (loop until finishp
          collect
             (progn
               (unless forms
                 (setq finishp (null forms)))
               (let ((tag next-form)
                     (current-forms (loop for current-form = (pop forms)
                                          do (setq next-form current-form)
                                          until (atom current-form)
                                          collect current-form)))
                 (cons tag current-forms))))))


;;;; MISCELLANEOUS UTILITIES
(defun disjointp (list1 list2)
  "Return true if LIST1 and LIST2 are disjoint as sets, false otherwise."
  (null (intersection list1 list2)))

(defmacro lazy-getf (plist indicator default)
  "Return (GETF PLIST INDICATOR) if INDICATOR exists in PLIST.  Otherwise, execute DEFAULT and return its results."
  (let ((sentinel (gensym))
        (result (gensym "RESULT")))
    `(let* ((,result (getf ,plist ,indicator ',sentinel)))
       (if (eq ,result ',sentinel)
           ,default
           ,result))))

