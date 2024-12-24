require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 (x0: El (type1467 a0 a1)) ≔ (∀ (λ y0 : El a0, (= ((@ITLIST a0 a1) x0 (@NIL a1) y0) y0)));
symbol term1 a0 a1 (x0: El (type1467 a0 a1)) ≔ ((λ y0 : El (type1467 a0 a1), (∀ (λ y1 : El a0, (= ((@ITLIST a0 a1) y0 (@NIL a1) y1) y1)))) x0);
symbol term3 a0 a1 (x0: El (type1467 a0 a1)) (x1: El a0) ≔ ((λ y0 : El a0, (= ((@ITLIST a0 a1) x0 (@NIL a1) y0) y0)) x1);
symbol term0 a0 a1 ≔ (∀ (λ y0 : El (type1467 a0 a1), (∀ (λ y1 : El a0, (= ((@ITLIST a0 a1) y0 (@NIL a1) y1) y1)))));
