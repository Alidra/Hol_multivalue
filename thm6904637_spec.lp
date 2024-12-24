require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6904637 : Prf (= (= ((@ε int) (λ x : El int, (∀ (λ y : El int, (∧ (= (int_mul x y) y) (= (int_mul y x) y)))))) (int_of_num (NUMERAL (BIT1 _0)))) (= ((@neutral int) int_mul) (int_of_num (NUMERAL (BIT1 _0)))));
