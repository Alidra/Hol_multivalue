require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301108 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (int_mul x (int_add y z)) (int_add (int_mul x y) (int_mul x z)))))))));
