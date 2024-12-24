require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.NEUTRAL_INT_MUL_term_abbrevs;
require open hol-light.thm6904637_spec;
require open hol-light.thm6905935_spec;
opaque symbol lem6905936 : Prf (= ((@neutral int) int_mul) term0) ≔ EQ_MP (@lem6904637) (@lem6905935);
