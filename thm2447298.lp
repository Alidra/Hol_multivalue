require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2447298_term_abbrevs;
opaque symbol lem2447298 (b : El int) (a : El int) : Prf (= (term0 b a) (= (int_divides a b) (term1 b a))) ≔ REFL (term0 b a);
