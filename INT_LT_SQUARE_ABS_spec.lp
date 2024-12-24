require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304970 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_lt (int_abs x) (int_abs y)) (int_lt (int_pow x (NUMERAL (BIT0 (BIT1 _0)))) (int_pow y (NUMERAL (BIT0 (BIT1 _0))))))))));
