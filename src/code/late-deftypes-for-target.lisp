(in-package "SB!KERNEL")

(sb!xc:deftype compiled-function ()
  '(and function
        #!+sb-eval (not sb!eval:interpreted-function)
        #!+sb-eval (not sb!eval2:minimally-compiled-function)))
