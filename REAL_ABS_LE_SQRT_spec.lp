require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1977057 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (real_le (real_abs (real_sub (sqrt x) (sqrt y))) (sqrt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 _0)))) (real_abs (real_sub x y)))))))));
