require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1980266_term_abbrevs;
opaque symbol lem1980266 (y : El real) (x : El real) : Prf (= (term0 y x) (= (real_gt x y) (real_lt y x))) ≔ REFL (term0 y x);
