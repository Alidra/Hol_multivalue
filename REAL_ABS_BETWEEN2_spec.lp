require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1550986 : Prf (∀ (λ x0 : El real, (∀ (λ x : El real, (∀ (λ y0 : El real, (∀ (λ y : El real, (⇒ (∧ (real_lt x0 y0) (∧ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (real_abs (real_sub x x0))) (real_sub y0 x0)) (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (real_abs (real_sub y y0))) (real_sub y0 x0)))) (real_lt x y))))))))));
