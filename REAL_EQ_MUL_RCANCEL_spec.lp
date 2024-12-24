require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1587429 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (= (real_mul x z) (real_mul y z)) (∨ (= x y) (= z (real_of_num (NUMERAL _0)))))))))));
