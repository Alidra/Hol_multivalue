require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2589738 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (div (int_neg m) (int_neg n)) ((@COND int) (= (rem m n) (int_of_num (NUMERAL _0))) (div m n) (int_add (div m n) (int_sgn n))))))));
