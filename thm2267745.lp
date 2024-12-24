require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2267745_term_abbrevs;
opaque symbol lem2267745 (a : El int) : Prf (= (term0 a) (= (term1 a) a)) ≔ REFL (term0 a);
