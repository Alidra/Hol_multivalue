require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El (list a1), (= ((@ZIP a0 a1) (@NIL a0) y0) (@NIL (prod a0 a1)))));
symbol term1 a0 a1 (x0: El (list a1)) ≔ ((λ y0 : El (list a1), (= ((@ZIP a0 a1) (@NIL a0) y0) (@NIL (prod a0 a1)))) x0);
