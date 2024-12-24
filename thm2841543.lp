require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841543_term_abbrevs;
require open hol-light.thm2841542_spec;
opaque symbol lem2841543 (x : El int) (y : El int) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem2841542 x y);
