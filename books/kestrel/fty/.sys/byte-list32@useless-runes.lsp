(BYTE-LIST32P)
(BOOLEANP-OF-BYTE-LIST32P)
(BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE)
(BYTE-LISTP-WHEN-BYTE-LIST32P-FORWARD)
(LEN-WHEN-BYTE-LIST32P-TAU)
(BYTE-LIST32-FIX
 (1 1 (:TYPE-PRESCRIPTION BYTE-LIST32-FIX))
 )
(BYTE-LIST32P-OF-BYTE-LIST32-FIX
 (155 16 (:REWRITE BYTE-LISTP-WHEN-BYTE-LIST32P-REWRITE))
 (146 2 (:REWRITE BYTE-LIST-FIX-WHEN-BYTE-LISTP))
 (72 6 (:REWRITE BYTE-LISTP-OF-TAKE))
 (68 12 (:DEFINITION LEN))
 (40 16 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (32 32 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (28 2 (:REWRITE TAKE-OF-TOO-MANY))
 (28 2 (:REWRITE BYTE-LIST-FIX-OF-TAKE))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (24 12 (:REWRITE DEFAULT-+-2))
 (24 2 (:REWRITE TAKE-OF-LEN-FREE))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-+-1))
 (11 11 (:TYPE-PRESCRIPTION BYTE-LIST32-FIX))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION NFIX))
 (4 4 (:REWRITE CONSP-OF-TAKE))
 (2 2 (:REWRITE TAKE-WHEN-ATOM))
 )
(BYTE-LIST32-FIX-WHEN-BYTE-LIST32P)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (33 33 (:TYPE-PRESCRIPTION BYTE-LIST32-FIX))
 )
(BYTE-LIST32-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION BYTE-LIST32-FIX))
 )
(BYTE-LIST32-EQUIV-IS-AN-EQUIVALENCE)
(BYTE-LIST32-EQUIV-IMPLIES-EQUAL-BYTE-LIST32-FIX-1)
(BYTE-LIST32-FIX-UNDER-BYTE-LIST32-EQUIV)
(EQUAL-OF-BYTE-LIST32-FIX-1-FORWARD-TO-BYTE-LIST32-EQUIV)
(EQUAL-OF-BYTE-LIST32-FIX-2-FORWARD-TO-BYTE-LIST32-EQUIV)
(BYTE-LIST32-EQUIV-OF-BYTE-LIST32-FIX-1-FORWARD)
(BYTE-LIST32-EQUIV-OF-BYTE-LIST32-FIX-2-FORWARD)
