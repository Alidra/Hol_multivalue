require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2318495 (x : El int) (y : El int) : Prf (∧ (= (¬ (int_le x y)) (int_le (int_add y (int_of_num (NUMERAL (BIT1 _0)))) x)) (∧ (= (¬ (int_lt x y)) (int_le y x)) (∧ (= (¬ (= x y)) (∨ (int_le (int_add x (int_of_num (NUMERAL (BIT1 _0)))) y) (int_le (int_add y (int_of_num (NUMERAL (BIT1 _0)))) x))) (= (int_lt x y) (int_le (int_add x (int_of_num (NUMERAL (BIT1 _0)))) y)))));
