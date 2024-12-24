require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301438 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_mul (int_add x y) (int_sub x y)) (int_sub (int_mul x x) (int_mul y y)))))));
