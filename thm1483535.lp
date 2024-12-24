require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483535_term_abbrevs;
require open hol-light.thm1483532_spec;
opaque symbol lem1483535 (y : El real) (x : El real) : Prf (= (term0 x y) (term1 y x)) ≔ ∧ₑ₁ (@lem1483532 x y);
