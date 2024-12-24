require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type1223 a0 a1)) ≔ ((λ y0 : El (type1223 a0 a1), (= (∀ (λ y1 : El (prod a1 a0), (y0 y1))) (∀ (λ y1 : El a1, (∀ (λ y2 : El a0, (y0 ((@̦‚ a1 a0) y1 y2)))))))) x0);
