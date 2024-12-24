require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1704991 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (⇒ (real_le (real_of_num (NUMERAL _0)) x) (real_le (real_add (real_of_num (NUMERAL (BIT1 _0))) (real_mul (real_of_num n) x)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 _0))) x) n)))))));
