require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_EQ_term_abbrevs;
require open hol-light.thm521920_spec;
require open hol-light.thm522075_spec;
opaque symbol lem522076 : Prf term0 ≔ EQ_MP (@lem521920) (@lem522075);
