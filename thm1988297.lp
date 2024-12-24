require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988297_term_abbrevs;
require open hol-light.thm1988294_spec;
opaque symbol lem1988297 (x : El real) (y : El real) : Prf (= (term0 x y) (term1 x y)) ≔ ∧ₑ₁ (@lem1988294 x y);
