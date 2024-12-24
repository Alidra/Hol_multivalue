require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 ≔ ((@= bool) (⇒ F (¬ F)));
symbol term0 ≔ (⇒ F (¬ F));
symbol term2 (x0: El bool) ≔ (⇒ x0 (¬ x0));
