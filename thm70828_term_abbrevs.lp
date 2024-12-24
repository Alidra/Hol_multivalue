require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El ind, (∀ (λ y1 : El ind, (= (= (IND_SUC y0) (IND_SUC y1)) (= y0 y1))))));
