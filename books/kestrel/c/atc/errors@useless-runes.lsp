(TMP-DEFTYPES-ANY-P$INLINE-OF-IDENTITY)
(TMP-DEFTYPES-IDENTITY-WHEN-ANY-P$INLINE (3 3 (:TYPE-PRESCRIPTION IDENTITY)))
(C::ERRORP (2 2 (:DEFINITION STRIP-CARS)))
(C::CONSP-WHEN-ERRORP)
(C::TAG-WHEN-ERRORP)
(C::ERRORP-WHEN-WRONG-TAG)
(C::ERROR-FIX$INLINE (6 6 (:TYPE-PRESCRIPTION IDENTITY)))
(C::ERRORP-OF-ERROR-FIX
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1
    (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV)))
(C::ERROR-FIX-WHEN-ERRORP (2 2 (:DEFINITION STRIP-CARS)))
(C::ERROR-FIX$INLINE (6 6 (:TYPE-PRESCRIPTION IDENTITY))
                     (2 2 (:DEFINITION STRIP-CARS)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(C::ERROR-EQUIV$INLINE)
(C::ERROR-EQUIV-IS-AN-EQUIVALENCE)
(C::ERROR-EQUIV-IMPLIES-EQUAL-ERROR-FIX-1)
(C::ERROR-FIX-UNDER-ERROR-EQUIV)
(C::EQUAL-OF-ERROR-FIX-1-FORWARD-TO-ERROR-EQUIV)
(C::EQUAL-OF-ERROR-FIX-2-FORWARD-TO-ERROR-EQUIV)
(C::ERROR-EQUIV-OF-ERROR-FIX-1-FORWARD)
(C::ERROR-EQUIV-OF-ERROR-FIX-2-FORWARD)
(C::TAG-OF-ERROR-FIX)
(C::ERROR->INFO$INLINE (20 20 (:TYPE-PRESCRIPTION IDENTITY))
                       (2 2 (:DEFINITION STRIP-CARS)))
(C::ANY-P-OF-ERROR->INFO)
(C::ERROR->INFO$INLINE-OF-ERROR-FIX-X
     (24 16 (:TYPE-PRESCRIPTION IDENTITY))
     (12 4 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
     (8 8 (:TYPE-PRESCRIPTION C::ERRORP)))
(C::ERROR->INFO$INLINE-OF-ERROR-FIX-X-NORMALIZE-CONST)
(C::ERROR->INFO$INLINE-ERROR-EQUIV-CONGRUENCE-ON-X)
(C::ERROR)
(C::ERRORP-OF-ERROR
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1
    (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV)))
(C::ERROR->INFO-OF-ERROR (35 27 (:TYPE-PRESCRIPTION IDENTITY)))
(C::ERROR-OF-FIELDS (3 1 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
                    (2 2 (:TYPE-PRESCRIPTION C::ERRORP)))
(C::ERROR-FIX-WHEN-ERROR (3 1 (:REWRITE C::ERROR-FIX-WHEN-ERRORP))
                         (2 2 (:TYPE-PRESCRIPTION C::ERRORP)))
(C::EQUAL-OF-ERROR
     (16 16
         (:REWRITE C::ERROR->INFO$INLINE-OF-ERROR-FIX-X-NORMALIZE-CONST)))
(C::ERROR-OF-IDENTITY-INFO)
(C::ERROR-OF-IDENTITY-INFO-NORMALIZE-CONST)
(C::ERROR-EQUAL-CONGRUENCE-ON-INFO)
(C::ERROR-FIX-REDEF)
(C::TAG-OF-ERROR)