((fstar-mode
  (fstar-subp-sloppy . nil)
  (eval .
	(progn (defun my-fstar-compute-prover-args-using-make ()
		 "Construct arguments to pass to F* by calling make."
		 (with-demoted-errors "Error when constructing arg string: %S"
		   (split-string
		    (car (last (process-lines "make"
					      "-C" (append (getenv "FSTAR_SOURCES_ROOT") "/src")
					      "-f" "Makefile.edit" "--quiet"
					      (concat (file-name-nondirectory buffer-file-name) "-dev")
					      )
			       )
			 )
		    )
		   )
		 )
	       (setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
	       )
	)
  )
 )

