require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1980259 (y : El real) (x : El real) : Prf ((λ x' : El real, (= (real_ge x' y) (real_le y x'))) x);
