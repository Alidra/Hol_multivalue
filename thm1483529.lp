require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483529_term_abbrevs;
require open hol-light.thm1483526_spec;
opaque symbol lem1483529 (x : El real) (y : El real) : Prf (= (= x y) (= (real_sub x y) term0)) ≔ ∧ₑ₁ (@lem1483526 x y);
