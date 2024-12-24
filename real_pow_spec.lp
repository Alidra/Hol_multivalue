require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1344316 (x : El real) : Prf (∧ (= (real_pow x (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0)))) (∀ (λ n : El num, (= (real_pow x (SUC n)) (real_mul x (real_pow x n))))));
