require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm161368_term_abbrevs;
require open hol-light.thm161353_spec;
opaque symbol lem161368 (m : El num) : Prf (term0 m) ≔ λ n : El num, (@lem161353 n m);
