require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418320_term_abbrevs;
require open hol-light.thm5418319_spec;
opaque symbol lem5418320 : Prf term0 ≔ λ m : El num, (@lem5418319 m);
