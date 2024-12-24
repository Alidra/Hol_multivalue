require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1645942 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_lt (real_abs x) (real_abs y)) (real_lt (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) (real_pow y (NUMERAL (BIT0 (BIT1 _0))))))))));
