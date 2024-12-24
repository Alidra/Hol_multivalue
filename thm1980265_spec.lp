require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1980265 (y : El real) (x : El real) : Prf ((λ x' : El real, (= (real_gt x' y) (real_lt y x'))) x);
