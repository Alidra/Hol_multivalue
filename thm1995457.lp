require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1995457_term_abbrevs;
opaque symbol lem1995457 (x : El real) (y : El real) : Prf (= (term0 x y) (= (real_div x y) (term1 x y))) ≔ REFL (term0 x y);
