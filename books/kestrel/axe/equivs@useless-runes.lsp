(EQUIVP)
(EQUIVP-FORWARD-TO-SYMBOLP)
(EQUIV-LISTP)
(EQUIVP-OF-CAR-WHEN-EQUIV-LISTP (1 1 (:REWRITE DEFAULT-CAR)))
(EQUIV-LISTP-OF-CDR (4 1
                       (:REWRITE EQUIVP-OF-CAR-WHEN-EQUIV-LISTP))
                    (1 1 (:REWRITE DEFAULT-CDR))
                    (1 1 (:REWRITE DEFAULT-CAR)))
(EQUIV-LIST-LISTP)
(SYMBOL-TO-EQUIVS-ALISTP)
(SYMBOL-TO-EQUIVS-ALISTP-FORWARD-TO-SYMBOL-ALISTP)
(EQUIV-LISTP-OF-LOOKUP-EQUAL-WHEN-SYMBOL-TO-EQUIVS-ALISTP
     (52 50 (:REWRITE DEFAULT-CAR))
     (39 37 (:REWRITE DEFAULT-CDR))
     (15 5 (:REWRITE EQUIV-LISTP-OF-CDR))
     (11 11
         (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
     (11 11
         (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP)))
(ALL-SYMBOL-TO-EQUIVS-ALISTP)
(SYMBOL-TO-EQUIVS-ALISTP-OF-LOOKUP-EQUAL-WHEN-ALL-SYMBOL-TO-EQUIVS-ALISTP-OF-STRIP-CDRS
     (36 33 (:REWRITE DEFAULT-CAR))
     (28 25 (:REWRITE DEFAULT-CDR)))
(SYMBOL-ALISTP-OF-LOOKUP-EQUAL-WHEN-ALL-SYMBOL-TO-EQUIVS-ALISTP-OF-STRIP-CDRS
     (51 48 (:REWRITE DEFAULT-CAR))
     (33 30 (:REWRITE DEFAULT-CDR)))
(EQUIV-ALISTP)
(GET-EQUIVS)
(EQUIV-LISTP-OF-GET-EQUIVS)