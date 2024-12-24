require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1648695 : Prf (∀ (λ n : El num, (= (real_pow (real_of_num (NUMERAL _0)) n) ((@COND real) (= n (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0))) (real_of_num (NUMERAL _0))))));
