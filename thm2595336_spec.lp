require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2595336 : Prf (∧ (∀ (λ n : El int, (= (div n (int_of_num (NUMERAL (BIT1 _0)))) n))) (∀ (λ n : El int, (= (rem n (int_of_num (NUMERAL (BIT1 _0)))) (int_of_num (NUMERAL _0))))));
