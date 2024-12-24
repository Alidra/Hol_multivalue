require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.NEUTRAL_INT_ADD_term_abbrevs;
require open hol-light.thm6914239_spec;
require open hol-light.thm6915505_spec;
opaque symbol lem6915506 : Prf (= ((@neutral int) int_add) term0) ≔ EQ_MP (@lem6914239) (@lem6915505);
