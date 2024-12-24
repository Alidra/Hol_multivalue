require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El bool) ≔ (∧ (⇒ x0 F) (⇒ F x0));
symbol term1 (x0: El bool) ≔ ((λ y0 : El bool, y0) x0);
symbol term0 ≔ (∀ (λ y0 : El bool, y0));
symbol term3 (x0: El bool) ≔ (⇒ (¬ x0) (= x0 F));
