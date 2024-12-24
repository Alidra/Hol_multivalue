require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1813_term_abbrevs;
opaque symbol lem1813 [A] (t : El bool) : Prf (= (term0 A t) (= (term1 A t) t)) ≔ REFL (term0 A t);
