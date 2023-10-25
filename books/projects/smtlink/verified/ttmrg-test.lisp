  ; a few test-cases to illustrate ttmrg and related functions
  (local
    (define ttmrg-example ()
      :returns (tterm ttmrg-p)
      (b* ((x   (make-ttmrg :guts (make-ttmrg-guts-var :name 'x)
			    :judgements (list '(integerp smt::tt-x)
					      '(rationalp smt::tt-x)
					      '(not (< smt::tt-x '0)))))
	   (y   (make-ttmrg :guts (make-ttmrg-guts-var :name 'y)
			    :judgements (list '(rationalp smt::tt-x))))
	   (two (make-ttmrg :guts (make-ttmrg-guts-quote :val '2)
			    :judgements (list '(integerp smt::tt-x)
					      '(rationalp smt::tt-x)
					      '(< '0 smt::tt-x))))
	   (x<2 (make-ttmrg :guts (make-ttmrg-guts-fncall :f '< :args (list x two))
			    :judgements (list '(booleanp smt::tt-x))))
	   (fx2 (make-ttmrg :guts (make-ttmrg-guts-fncall :f 'f :args (list x two))))
	   (gxy (make-ttmrg :guts (make-ttmrg-guts-fncall :f 'g :args (list x y))))
	   (ifx (make-ttmrg :guts (make-ttmrg-guts-if :condx x<2 :thenx fx2 :elsex gxy))))
	ifx)
      ///
      (make-test
	(equal
	  (ttmrg->term (ttmrg-example))
	  '(if (< x '2) (f x '2) (g x y)))
	:name ttmrg->term--test
	:output (:fail (:all . :warn)))))

  (must-succeed (acl2::rule
    (equal (ttmrg->judgements--eval 
	     (make-ttmrg
	       :guts (make-ttmrg-guts-var :name 'x)
	       :judgements (list '(integerp smt::tt-x)
				 '(rationalp smt::tt-x)))
	     (list (cons 'x 42) (cons 'y foo)))
	   t)
    :in-theory (e/d (ttmrg->judgements--eval ttmrg->judgements--eval-help))))

  (must-succeed (acl2::rule
    (equal (ttmrg->judgements--eval 
	     (make-ttmrg
	       :guts (make-ttmrg-guts-var :name 'x)
	       :judgements (list '(integerp smt::tt-x)
				 '(rationalp smt::tt-x)))
	     (list (cons 'x nil) (cons 'y foo)))
	   nil)
    :in-theory (e/d (ttmrg->judgements--eval ttmrg->judgements--eval-help)))))
