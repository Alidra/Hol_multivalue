require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1988299_term_abbrevs;
require open hol-light.thm1988296_spec;
opaque symbol lem1988299 (y : El real) (x : El real) : Prf (= (term0 x y) (term1 y x)) ≔ ∧ₑ₁ (@lem1988296 x y);
