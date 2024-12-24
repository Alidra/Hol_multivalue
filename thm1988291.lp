require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988291_term_abbrevs;
require open hol-light.thm1988288_spec;
opaque symbol lem1988291 (x : El real) (y : El real) : Prf (= (real_ge x y) (term0 x y)) ≔ ∧ₑ₁ (@lem1988288 x y);
