require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1058227_term_abbrevs;
opaque symbol lem1058227 [A] : Prf (= (term0 A) (term0 A)) ≔ REFL (term0 A);
