require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El bool) ≔ (∀ (λ y0 : El bool, (= (¬ (⇒ x0 y0)) (∧ x0 (¬ y0)))));
symbol term0 (x0: El bool) ≔ ((λ y0 : El bool, (∀ (λ y1 : El bool, (= (¬ (⇒ y0 y1)) (∧ y0 (¬ y1)))))) x0);
symbol term2 (x0: El bool) (x1: El bool) ≔ ((λ y0 : El bool, (= (¬ (⇒ x0 y0)) (∧ x0 (¬ y0)))) x1);
