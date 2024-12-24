require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416570 (p : El num) (y : El int) (z : El int) (x : El int) (q : El num) : Prf (∧ (= (int_mul x x) (int_pow x (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (int_pow (int_mul x y) q) (int_mul (int_pow x q) (int_pow y q))) (∧ (= (int_pow (int_pow x p) q) (int_pow x (* p q))) (∧ (= (int_pow x (NUMERAL _0)) (int_of_num (NUMERAL (BIT1 _0)))) (∧ (= (int_pow x (NUMERAL (BIT1 _0))) x) (∧ (= (int_mul x (int_add y z)) (int_add (int_mul x y) (int_mul x z))) (= (int_pow x (SUC q)) (int_mul x (int_pow x q)))))))));
