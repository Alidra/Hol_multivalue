require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2746101 : Prf (∀ (λ n : El int, (∀ (λ k : El num, (= (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) (int_pow n k)) (∧ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 _0)))) n) (¬ (= k (NUMERAL _0)))))))));
