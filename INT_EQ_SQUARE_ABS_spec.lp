require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301903 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_abs x) (int_abs y)) (= (int_pow x (NUMERAL (BIT0 (BIT1 _0)))) (int_pow y (NUMERAL (BIT0 (BIT1 _0))))))))));
