require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2586280 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (div (int_neg m) n) ((@COND int) (= (rem m n) (int_of_num (NUMERAL _0))) (int_neg (div m n)) (int_sub (int_neg (div m n)) (int_sgn n))))))));
