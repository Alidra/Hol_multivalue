require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1982797 (x : El real) (y : El real) : Prf (= ((λ y' : El real, (= (real_div x y') (real_mul x (real_inv y')))) y) (= (real_div x y) (real_mul x (real_inv y))));
