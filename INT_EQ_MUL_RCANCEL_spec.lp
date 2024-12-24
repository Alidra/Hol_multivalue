require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301754 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (= (int_mul x z) (int_mul y z)) (∨ (= x y) (= z (int_of_num (NUMERAL _0)))))))))));
