require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2802699 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (int_lcm ((@̦‚ int int) m n)) ((@COND int) (= (int_mul m n) (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0)) (div (int_abs (int_mul m n)) (int_gcd ((@̦‚ int int) m n)))))))));
