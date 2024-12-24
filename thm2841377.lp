require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841377_term_abbrevs;
require open hol-light.thm2841336_spec;
opaque symbol lem2841377 (k : El num) (n : El num) : Prf (term0 k n) ≔ (@lem2841336 k) n;
