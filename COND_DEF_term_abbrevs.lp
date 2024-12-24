require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (λ y0 : El bool, (λ y1 : El a0, (λ y2 : El a0, ((@ε a0) (λ y3 : El a0, (∧ (⇒ (= y0 T) (= y3 y1)) (⇒ (= y0 F) (= y3 y2))))))));
