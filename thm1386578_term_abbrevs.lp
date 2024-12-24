require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El bool) ≔ (¬ (¬ x0));
symbol term0 (x0: El bool) ≔ (⇒ (¬ x0) F);
symbol term3 (x0: El bool) ≔ (⇒ (⇒ (¬ x0) F) x0);
symbol term2 (x0: El bool) ≔ (⇒ (⇒ (¬ x0) F));
