(in-package "SB!EVAL2")

(sb!kernel::!defstruct-with-alternate-metaclass
 minimally-compiled-function
 :slot-names (name lambda-list documentation source-location source-path)
 :boa-constructor %make-minimally-compiled-function
 :superclass-name function
 :metaclass-name sb!kernel:static-classoid
 :metaclass-constructor sb!kernel:make-static-classoid
 :dd-type sb!kernel:funcallable-structure
 :runtime-type-checks-p nil)

#-sb-xc-host
(progn
  (defun make-minimally-compiled-function
      (name lambda-list documentation source-location source-path function)
    (let ((mincfun (%make-minimally-compiled-function
                    name lambda-list documentation source-location source-path)))
      (setf (sb!kernel:funcallable-instance-fun mincfun) function)
      mincfun))

  (defun minimally-compiled-function-p (function)
    (typep function 'minimally-compiled-function))

  (sb!int:def!method print-object ((obj minimally-compiled-function) stream)
    (print-unreadable-object (obj stream
                              :identity (not (minimally-compiled-function-name obj)))
      (format stream "~A ~A" '#:minimally-compiled-function
              (minimally-compiled-function-name obj)))))