require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (⇒ (¬ F) F);
symbol term3 (x0: El bool) ≔ (¬ (¬ x0));
symbol term4 (x0: El bool) ≔ (⇒ (¬ x0) x0);
symbol term2 ≔ (¬ (¬ F));
symbol term1 ≔ (¬ (⇒ (¬ F) F));
