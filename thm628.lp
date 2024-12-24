require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm626_spec;
require open hol-light.thm627_spec;
opaque symbol lem628 (p : El bool) : Prf (= (∧ p p) p) ≔ EQ_MP (@lem627 p) (@lem626 p);
