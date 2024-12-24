require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 ≔ (⇒ F (¬ T));
symbol term4 ≔ (∧ (⇒ (¬ T) F) (⇒ F (¬ T)));
symbol term1 ≔ ((@= bool) (¬ T));
symbol term2 ≔ (⇒ (¬ T) F);
symbol term0 ≔ ((λ y0 : El bool, (⇒ y0 F)) T);
