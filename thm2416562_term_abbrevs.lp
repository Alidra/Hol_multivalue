require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El int) (x1: El int) (x2: El int) (x3: El num) (x4: El int) (x5: El int) (x6: El int) (x7: El num) ≔ (∧ (= (int_add x0 (int_add x1 x2)) (int_add (int_add x0 x1) x2)) (∧ (= (int_mul (int_pow x6 x3) (int_pow x6 x7)) (int_pow x6 (+ x3 x7))) (∧ (= (int_mul x6 (int_pow x6 x7)) (int_pow x6 (SUC x7))) (∧ (= (int_mul (int_pow x6 x7) x6) (int_pow x6 (SUC x7))) (∧ (= (int_mul x6 x6) (int_pow x6 (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (int_pow (int_mul x6 x4) x7) (int_mul (int_pow x6 x7) (int_pow x4 x7))) (∧ (= (int_pow (int_pow x6 x3) x7) (int_pow x6 (* x3 x7))) (∧ (= (int_pow x6 (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0)))) (∧ (= (int_pow x6 (NUMERAL (BIT1 _0))) x6) (∧ (= (int_mul x6 (int_add x4 x5)) (int_add (int_mul x6 x4) (int_mul x6 x5))) (= (int_pow x6 (SUC x7)) (int_mul x6 (int_pow x6 x7)))))))))))));
