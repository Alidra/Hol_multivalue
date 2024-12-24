require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type1470 a0 a1)) (x1: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@ALLPAIRS a0 a1) x0 (@NIL a1) y0) T)) x1);
