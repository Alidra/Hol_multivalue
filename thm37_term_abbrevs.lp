require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El bool) (x1: El bool) ≔ (⇒ (= x0 x1) (⇒ x0 x1));
