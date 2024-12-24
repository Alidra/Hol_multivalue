require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483525_term_abbrevs;
require open hol-light.thm1483522_spec;
opaque symbol lem1483525 (x : El real) (y : El real) : Prf (= (real_gt x y) (term0 x y)) ≔ ∧ₑ₁ (@lem1483522 x y);
