require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm627_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem627 (p : El bool) : Prf (= (term0 p) (= (∧ p p) p)) ≔ (@lem32 (∧ p p) p);
