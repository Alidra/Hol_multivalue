require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) ≔ (∧ (= (¬ (= x0 x1)) (∨ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 _0)))) x1) (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 _0)))) x0))) (= (int_lt x0 x1) (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 _0)))) x1)));
