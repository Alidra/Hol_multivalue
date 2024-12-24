require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841589_term_abbrevs;
opaque symbol lem2841589 (x : El int) : Prf (= (term0 x) (= (term1 x) (term2 x))) ≔ REFL (term0 x);
