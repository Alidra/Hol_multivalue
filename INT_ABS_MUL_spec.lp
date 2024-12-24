require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300430 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_abs (int_mul x y)) (int_mul (int_abs x) (int_abs y)))))));
