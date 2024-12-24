require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2310379 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (int_mul (int_sub x y) z) (int_sub (int_mul x z) (int_mul y z)))))))));
