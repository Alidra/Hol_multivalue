require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2318057 (x : El int) : Prf (∧ (= (int_pow x (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0)))) (∀ (λ n : El num, (= (int_pow x (SUC n)) (int_mul x (int_pow x n))))));
