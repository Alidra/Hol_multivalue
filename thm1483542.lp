require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483542_term_abbrevs;
require open hol-light.thm1483540_spec;
opaque symbol lem1483542 (x : El real) (y : El real) : Prf (term0 x y) ≔ ∧ₑ₂ (@lem1483540 x y);
