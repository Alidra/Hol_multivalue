require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988289_term_abbrevs;
require open hol-light.thm1988286_spec;
opaque symbol lem1988289 (x : El real) (y : El real) : Prf (= (real_gt x y) (term0 x y)) ≔ ∧ₑ₁ (@lem1988286 x y);
