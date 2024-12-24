require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308188 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (⇒ (int_le (int_of_num (NUMERAL _0)) x) (int_le (int_add (int_of_num (NUMERAL (BIT1 _0))) (int_mul (int_of_num n) x)) (int_pow (int_add (int_of_num (NUMERAL (BIT1 _0))) x) n)))))));
