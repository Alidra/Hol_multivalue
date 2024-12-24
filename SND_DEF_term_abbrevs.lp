require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 a1 (x0: El (prod a0 a1)) ≔ ((@ε a1) (λ y0 : El a1, (∃ (λ y1 : El a0, (= x0 ((@̦‚ a0 a1) y1 y0))))));
symbol term0 a0 a1 ≔ (λ y0 : El (prod a0 a1), ((@ε a1) (λ y1 : El a1, (∃ (λ y2 : El a0, (= y0 ((@̦‚ a0 a1) y2 y1)))))));
symbol term1 a0 a1 (x0: El (prod a0 a1)) ≔ ((λ y0 : El (prod a0 a1), ((@ε a1) (λ y1 : El a1, (∃ (λ y2 : El a0, (= y0 ((@̦‚ a0 a1) y2 y1))))))) x0);
symbol term3 a0 a1 ≔ (∀ (λ y0 : El (prod a0 a1), (= ((@SND a0 a1) y0) ((@ε a1) (λ y1 : El a1, (∃ (λ y2 : El a0, (= y0 ((@̦‚ a0 a1) y2 y1)))))))));
