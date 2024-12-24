require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483554_term_abbrevs;
require open hol-light.thm1483552_spec;
opaque symbol lem1483554 (x : El real) (y : El real) : Prf (= (term0 x y) (term1 x y)) ≔ ∧ₑ₂ (@lem1483552 x y);
