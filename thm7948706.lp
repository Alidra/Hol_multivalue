require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7948706_term_abbrevs;
require open hol-light.thm7948704_spec;
opaque symbol lem7948706 [A] (n : El num) : Prf (term0 A n) ≔ ∧ₑ₂ (@lem7948704 A n);
