require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338026 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_mul x y) (int_of_num (NUMERAL (BIT1 _0)))) (∨ (∧ (= x (int_of_num (NUMERAL (BIT1 _0)))) (= y (int_of_num (NUMERAL (BIT1 _0))))) (∧ (= x (int_neg (int_of_num (NUMERAL (BIT1 _0))))) (= y (int_neg (int_of_num (NUMERAL (BIT1 _0))))))))))));
