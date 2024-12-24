require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ ((@ε ind) (λ y0 : El ind, (∧ (∀ (λ y1 : El ind, (∀ (λ y2 : El ind, (= (= (IND_SUC y1) (IND_SUC y2)) (= y1 y2)))))) (∀ (λ y1 : El ind, (¬ (= (IND_SUC y1) y0)))))));
