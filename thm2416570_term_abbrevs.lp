require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El int) (x2: El int) (x3: El int) (x4: El num) ≔ (∧ (= (int_mul x3 x3) (int_pow x3 (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (int_pow (int_mul x3 x1) x4) (int_mul (int_pow x3 x4) (int_pow x1 x4))) (∧ (= (int_pow (int_pow x3 x0) x4) (int_pow x3 (* x0 x4))) (∧ (= (int_pow x3 (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0)))) (∧ (= (int_pow x3 (NUMERAL (BIT1 _0))) x3) (∧ (= (int_mul x3 (int_add x1 x2)) (int_add (int_mul x3 x1) (int_mul x3 x2))) (= (int_pow x3 (SUC x4)) (int_mul x3 (int_pow x3 x4)))))))));
