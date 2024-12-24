require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3174157 : Prf (∀ (λ n : El int, (= (real_zpow (real_of_num (NUMERAL _0)) n) ((@COND real) (= n (int_of_num (NUMERAL _0))) (real_of_num (NUMERAL (BIT1 _0))) (real_of_num (NUMERAL _0))))));
