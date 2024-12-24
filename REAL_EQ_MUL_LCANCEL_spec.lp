require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1586590 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (= (real_mul x y) (real_mul x z)) (∨ (= x (real_of_num (NUMERAL _0))) (= y z)))))))));
