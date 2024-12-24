require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm21385_term_abbrevs;
require open hol-light.thm21384_spec;
opaque symbol lem21385 [A] (x : El A) (y : El A) (z : El A) : Prf (term0 A x y z) ≔ ∧ₑ₂ (@lem21384 A x y z);
