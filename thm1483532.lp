require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483532_term_abbrevs;
require open hol-light.thm1483530_spec;
opaque symbol lem1483532 (x : El real) (y : El real) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1483530 x y);
