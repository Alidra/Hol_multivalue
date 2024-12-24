require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 (x0: El bool) ≔ (∧ F (¬ x0));
symbol term3 (x0: El bool) ≔ (∧ (¬ T) (¬ x0));
symbol term0 (x0: El bool) ≔ (¬ (∨ T x0));
symbol term2 ≔ (∧ (¬ T));
symbol term1 (x0: El bool) ≔ ((@= bool) (¬ (∨ T x0)));
