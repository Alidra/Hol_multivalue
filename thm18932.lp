require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm18932_term_abbrevs;
opaque symbol lem18932 [A] (t : El bool) : Prf (= (term0 A t) (= (term1 A t) t)) ≔ REFL (term0 A t);
