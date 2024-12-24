require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338225 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_abs (int_mul x y)) (int_of_num (NUMERAL (BIT1 _0)))) (∧ (= (int_abs x) (int_of_num (NUMERAL (BIT1 _0)))) (= (int_abs y) (int_of_num (NUMERAL (BIT1 _0))))))))));
