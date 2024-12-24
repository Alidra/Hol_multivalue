require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.NEUTRAL_REAL_ADD_term_abbrevs;
require open hol-light.thm7064171_spec;
require open hol-light.thm7065437_spec;
opaque symbol lem7065438 : Prf (= ((@neutral real) real_add) term0) ≔ EQ_MP (@lem7064171) (@lem7065437);
