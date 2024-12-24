require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1344312_term_abbrevs;
require open hol-light.thm1344310_spec;
require open hol-light.thm1344311_spec;
opaque symbol lem1344312 (x : El real) : Prf (= (term0 x) term1) ≔ EQ_MP (@lem1344311 x) (@lem1344310 x);
