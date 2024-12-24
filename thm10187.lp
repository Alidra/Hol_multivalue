require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm10187_term_abbrevs;
require open hol-light.thm10164_spec;
opaque symbol lem10187 : Prf term0 ≔ λ t : El bool, (@lem10164 t);
