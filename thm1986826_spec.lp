require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1986826 : Prf (∧ (∀ (λ x : El real, (= (real_mul (real_of_num (NUMERAL _0)) x) (real_of_num (NUMERAL _0))))) (∧ (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (= (real_add x y) (real_add x z)) (= y z)))))))) (∀ (λ w : El real, (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (= (real_add (real_mul w y) (real_mul x z)) (real_add (real_mul w z) (real_mul x y))) (∨ (= w x) (= y z)))))))))))));
