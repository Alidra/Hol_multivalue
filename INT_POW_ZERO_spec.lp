require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308946 : Prf (∀ (λ n : El num, (= (int_pow (int_of_num (NUMERAL _0)) n) ((@COND int) (= n (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0))) (int_of_num (NUMERAL _0))))));
