require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 (x0: El a0) (x1: El (list a0)) (x2: El (list a1)) ≔ (∧ (= ((@ZIP a0 a1) (@NIL a0) x2) (@NIL (prod a0 a1))) (= ((@ZIP a0 a1) ((@CONS a0) x0 x1) x2) ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) x0 ((@HD a1) x2)) ((@ZIP a0 a1) x1 ((@TL a1) x2)))));
symbol term1 a0 a1 (x0: El a0) (x1: El (list a0)) (x2: El (list a1)) ≔ ((@CONS (prod a0 a1)) ((@̦‚ a0 a1) x0 ((@HD a1) x2)) ((@ZIP a0 a1) x1 ((@TL a1) x2)));
symbol term0 a0 a1 (x0: El a0) (x1: El (list a0)) (x2: El (list a1)) ≔ ((@ZIP a0 a1) ((@CONS a0) x0 x1) x2);
