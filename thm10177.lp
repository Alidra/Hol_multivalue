require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm10176_spec;
opaque symbol lem10177 : Prf (= (¬ T) F) ≔ EQ_MP (@lem10176) (@lem0);
