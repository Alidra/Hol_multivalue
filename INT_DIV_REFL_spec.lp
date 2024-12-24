require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2541192 : Prf (∀ (λ n : El int, (= (div n n) ((@COND int) (= n (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0)))))));
