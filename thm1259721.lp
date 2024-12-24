require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1259721_term_abbrevs;
require open hol-light.thm1259695_spec;
opaque symbol lem1259721 : Prf term0 ≔ λ m : El num, (@lem1259695 m);
