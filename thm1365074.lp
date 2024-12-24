require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm1365073_spec;
opaque symbol lem1365074 : Prf (= (∧ T F) F) ≔ EQ_MP (@lem1365073) (@lem0);
