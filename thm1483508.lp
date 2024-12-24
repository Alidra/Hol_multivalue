require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483508_term_abbrevs;
require open hol-light.thm1483505_spec;
opaque symbol lem1483508 (y : El real) (x : El real) (z : El real) : Prf (= (term0 x y z) (term1 y x z)) ≔ ∧ₑ₁ (@lem1483505 y z x (@el num));
