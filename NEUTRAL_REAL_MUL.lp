require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.NEUTRAL_REAL_MUL_term_abbrevs;
require open hol-light.thm6910119_spec;
require open hol-light.thm6911417_spec;
opaque symbol lem6911418 : Prf (= ((@neutral real) real_mul) term0) ≔ EQ_MP (@lem6910119) (@lem6911417);
