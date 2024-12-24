require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 a2 (x0: El a1) (x1: El (type1475 a0 a1 a2)) (x2: El (list a1)) (x3: El (list a2)) ≔ (∧ (= ((@MAP2 a0 a1 a2) x1 (@NIL a1) x3) (@NIL a0)) (= ((@MAP2 a0 a1 a2) x1 ((@CONS a1) x0 x2) x3) ((@CONS a0) (x1 x0 ((@HD a2) x3)) ((@MAP2 a0 a1 a2) x1 x2 ((@TL a2) x3)))));
symbol term1 a0 a1 a2 (x0: El a1) (x1: El (type1475 a0 a1 a2)) (x2: El (list a1)) (x3: El (list a2)) ≔ ((@CONS a0) (x1 x0 ((@HD a2) x3)) ((@MAP2 a0 a1 a2) x1 x2 ((@TL a2) x3)));
symbol term0 a0 a1 a2 (x0: El (type1475 a0 a1 a2)) (x1: El a1) (x2: El (list a1)) (x3: El (list a2)) ≔ ((@MAP2 a0 a1 a2) x0 ((@CONS a1) x1 x2) x3);
