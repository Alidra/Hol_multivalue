require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988287_term_abbrevs;
require open hol-light.thm1988284_spec;
opaque symbol lem1988287 (y : El real) (x : El real) : Prf (= (real_le x y) (term0 y x)) ≔ ∧ₑ₁ (@lem1988284 x y);
