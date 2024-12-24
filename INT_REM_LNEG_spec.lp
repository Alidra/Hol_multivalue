require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2586279 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (rem (int_neg m) n) ((@COND int) (= (rem m n) (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0)) (int_sub (int_abs n) (rem m n))))))));
