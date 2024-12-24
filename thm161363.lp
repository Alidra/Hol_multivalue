require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm161363_term_abbrevs;
require open hol-light.thm161358_spec;
opaque symbol lem161363 : Prf term0 ≔ λ m : El num, (@lem161358 m);
