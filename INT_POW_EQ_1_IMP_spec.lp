require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307966 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (⇒ (∧ (¬ (= n (NUMERAL _0))) (= (int_pow x n) (int_of_num (NUMERAL (BIT1 _0))))) (= (int_abs x) (int_of_num (NUMERAL (BIT1 _0)))))))));
