require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1999796_term_abbrevs;
opaque symbol lem1999796 (x : El real) (y : El real) : Prf (= (= (real_lt x y) (term0 x y)) (= (real_lt x y) (term0 x y))) ≔ REFL (= (real_lt x y) (term0 x y));
