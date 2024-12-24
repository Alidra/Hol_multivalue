require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El num) ≔ ((λ y0 : El num, (∀ (λ y1 : El (list a0), (= ((@EL a0) (SUC y0) y1) ((@EL a0) y0 ((@TL a0) y1)))))) x0);
symbol term1 a0 (x0: El num) ≔ (∀ (λ y0 : El (list a0), (= ((@EL a0) (SUC x0) y0) ((@EL a0) x0 ((@TL a0) y0)))));
symbol term2 a0 (x0: El num) (x1: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@EL a0) (SUC x0) y0) ((@EL a0) x0 ((@TL a0) y0)))) x1);
