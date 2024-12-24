require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988293_term_abbrevs;
require open hol-light.thm1988290_spec;
opaque symbol lem1988293 (x : El real) (y : El real) : Prf (= (= x y) (= (real_sub x y) term0)) ≔ ∧ₑ₁ (@lem1988290 x y);
