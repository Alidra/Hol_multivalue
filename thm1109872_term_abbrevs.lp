require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 a0 a1 (x0: El (type1470 a0 a1)) (x1: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@ALLPAIRS a0 a1) x0 (@NIL a1) y0) T)) x1);
symbol term0 a0 a1 ≔ (∀ (λ y0 : El (type1470 a0 a1), (∀ (λ y1 : El (list a0), (= ((@ALLPAIRS a0 a1) y0 (@NIL a1) y1) T)))));
symbol term2 a0 a1 (x0: El (type1470 a0 a1)) ≔ (∀ (λ y0 : El (list a0), (= ((@ALLPAIRS a0 a1) x0 (@NIL a1) y0) T)));
symbol term1 a0 a1 (x0: El (type1470 a0 a1)) ≔ ((λ y0 : El (type1470 a0 a1), (∀ (λ y1 : El (list a0), (= ((@ALLPAIRS a0 a1) y0 (@NIL a1) y1) T)))) x0);
