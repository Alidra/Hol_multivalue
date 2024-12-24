require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300215 : Prf (∀ (λ x0 : El int, (∀ (λ x : El int, (∀ (λ y0 : El int, (∀ (λ y : El int, (⇒ (∧ (int_lt x0 y0) (∧ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) (int_abs (int_sub x x0))) (int_sub y0 x0)) (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) (int_abs (int_sub y y0))) (int_sub y0 x0)))) (int_lt x y))))))))));
