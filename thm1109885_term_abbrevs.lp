require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El a1) (x1: El (type1470 a0 a1)) (x2: El (list a1)) (x3: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@ALLPAIRS a0 a1) x1 ((@CONS a1) x0 x2) y0) (∧ ((@ALL a0) (x1 x0) y0) ((@ALLPAIRS a0 a1) x1 x2 y0)))) x3);
symbol term1 a0 a1 (x0: El (type1470 a0 a1)) (x1: El a1) (x2: El (list a1)) (x3: El (list a0)) ≔ ((@ALLPAIRS a0 a1) x0 ((@CONS a1) x1 x2) x3);
symbol term2 a0 a1 (x0: El a1) (x1: El (type1470 a0 a1)) (x2: El (list a1)) (x3: El (list a0)) ≔ (∧ ((@ALL a0) (x1 x0) x3) ((@ALLPAIRS a0 a1) x1 x2 x3));
