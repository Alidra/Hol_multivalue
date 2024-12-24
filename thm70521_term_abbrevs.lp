require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε (fun ind ind)) (λ y0 : El (fun ind ind), (∃ (λ y1 : El ind, (∧ (∀ (λ y2 : El ind, (∀ (λ y3 : El ind, (= (= (y0 y2) (y0 y3)) (= y2 y3)))))) (∀ (λ y2 : El ind, (¬ (= (y0 y2) y1)))))))));
