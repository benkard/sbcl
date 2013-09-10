(defsystem "eval2"
  :version "1.0"
  :author "Matthias Benkard <code@mail.matthias.benkard.de>"
  :depends-on (#:alexandria #:closer-mop)
  :components ((:file "eval2-defpackage")
               #-sbcl (:file "early-eval2-generic")
               #+sbcl (:file "early-eval2")
               (:file "eval2-macros")
               (:file "eval2-types")
               (:file "eval2-util")
               (:file "eval2-generic")
               #+ccl (:file "eval2-ccl")
               #+sbcl (:file "eval2-sbcl")
               (:file "eval2")
               (:file "eval2-transformers")
               (:file "eval2-compiler"))
  :serial t)
