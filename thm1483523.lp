require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483523_term_abbrevs;
require open hol-light.thm1483520_spec;
opaque symbol lem1483523 (y : El real) (x : El real) : Prf (= (real_le x y) (term0 y x)) ≔ ∧ₑ₁ (@lem1483520 x y);
