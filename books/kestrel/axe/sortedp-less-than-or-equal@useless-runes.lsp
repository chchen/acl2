(SORTEDP-<= (5 5 (:REWRITE DEFAULT-CAR))
            (3 3 (:REWRITE DEFAULT-CDR)))
(SORTEDP-<=-OF-CDR (2 2
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                   (2 2 (:REWRITE DEFAULT-CAR))
                   (2 1 (:REWRITE DEFAULT-<-2))
                   (2 1 (:REWRITE DEFAULT-<-1)))