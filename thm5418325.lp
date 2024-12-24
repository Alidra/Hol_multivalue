require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418325_term_abbrevs;
require open hol-light.thm5418314_spec;
opaque symbol lem5418325 : Prf term0 ≔ λ m : El num, (@lem5418314 m);
