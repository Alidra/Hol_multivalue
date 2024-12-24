require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type1413 a0 a1)) (x1: El (list a1)) ≔ ((λ y0 : El (list a1), (= ((@ALL2 a0 a1) x0 (@NIL a0) y0) (= y0 (@NIL a1)))) x1);
