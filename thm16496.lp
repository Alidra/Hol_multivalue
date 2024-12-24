require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm16496_term_abbrevs;
require open hol-light.thm16495_spec;
opaque symbol lem16496 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem16495 t);
