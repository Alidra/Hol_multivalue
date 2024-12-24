require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 (x0: El a0) (x1: El (type1413 a0 a1)) (x2: El (list a0)) (x3: El (list a1)) ≔ ((@COND bool) (= x3 (@NIL a1)) F (∧ (x1 x0 ((@HD a1) x3)) ((@ALL2 a0 a1) x1 x2 ((@TL a1) x3))));
symbol term0 a0 a1 (x0: El a0) (x1: El (type1413 a0 a1)) (x2: El (list a0)) (x3: El (list a1)) ≔ ((λ y0 : El (list a1), (= ((@ALL2 a0 a1) x1 ((@CONS a0) x0 x2) y0) ((@COND bool) (= y0 (@NIL a1)) F (∧ (x1 x0 ((@HD a1) y0)) ((@ALL2 a0 a1) x1 x2 ((@TL a1) y0)))))) x3);
symbol term1 a0 a1 (x0: El (type1413 a0 a1)) (x1: El a0) (x2: El (list a0)) (x3: El (list a1)) ≔ ((@ALL2 a0 a1) x0 ((@CONS a0) x1 x2) x3);
