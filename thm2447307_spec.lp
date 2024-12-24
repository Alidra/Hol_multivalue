require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2447307 (x : El int) (y : El int) (n : El int) : Prf (= ((λ n' : El int, (= ((@== int) x y (int_mod n')) (∃ (λ d : El int, (= (int_sub x y) (int_mul n' d)))))) n) (= ((@== int) x y (int_mod n)) (∃ (λ d : El int, (= (int_sub x y) (int_mul n d))))));
