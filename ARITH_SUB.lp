require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_SUB_term_abbrevs;
require open hol-light.thm522778_spec;
require open hol-light.thm523589_spec;
opaque symbol lem523590 : Prf term0 ≔ EQ_MP (@lem522778) (@lem523589);
