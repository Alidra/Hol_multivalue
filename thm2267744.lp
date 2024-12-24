require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2267744_term_abbrevs;
require open hol-light.thm2267726_spec;
opaque symbol lem2267743 : Prf term0 ≔ λ a : El int, (@lem2267726 a);
opaque symbol lem2267744 (a : El int) : Prf (term1 a) ≔ (@lem2267743) a;
