((fstar-mode
  (fstar-subp-sloppy . nil)
  (eval . (defun fstar-subp-prover-args-for-compiler-hacking-fixed ()
	     "Compute arguments suitable for hacking on the F* compiler."
	     `("--lax"
	       ;; "--admit_smt_queries" "true"
	       "--MLish" "--warn_error" "-272"
	       "--include" "/home/lucas/FStar/fstar-missing-files/" 
	       ,@(-mapcat (lambda (dir) `("--include" ,dir))
			  (fstar-subp--prover-includes-for-compiler-hacking))))
	   )
  (fstar-subp-prover-args . fstar-subp-prover-args-for-compiler-hacking-fixed)))
