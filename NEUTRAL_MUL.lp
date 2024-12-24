require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.NEUTRAL_MUL_term_abbrevs;
require open hol-light.thm6898643_spec;
require open hol-light.thm6901231_spec;
opaque symbol lem6901232 : Prf (= ((@neutral num) *) term0) ≔ EQ_MP (@lem6898643) (@lem6901231);
