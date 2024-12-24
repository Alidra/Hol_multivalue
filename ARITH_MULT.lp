require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_MULT_term_abbrevs;
require open hol-light.thm514761_spec;
require open hol-light.thm515543_spec;
opaque symbol lem515544 : Prf term0 ≔ EQ_MP (@lem514761) (@lem515543);
