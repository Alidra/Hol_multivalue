require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1995457 (x : El real) (y : El real) : Prf (= ((λ y' : El real, (= (real_div x y') (real_mul x (real_inv y')))) y) (= (real_div x y) (real_mul x (real_inv y))));
