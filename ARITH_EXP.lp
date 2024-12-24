require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ARITH_EXP_term_abbrevs;
require open hol-light.thm515916_spec;
require open hol-light.thm516204_spec;
opaque symbol lem516205 : Prf term0 ≔ EQ_MP (@lem515916) (@lem516204);
