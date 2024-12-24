require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483495 (p : El num) (y : El real) (z : El real) (x : El real) (q : El num) : Prf (∧ (= (real_mul x x) (real_pow x (NUMERAL (BIT0 (BIT1 _0))))) (∧ (= (real_pow (real_mul x y) q) (real_mul (real_pow x q) (real_pow y q))) (∧ (= (real_pow (real_pow x p) q) (real_pow x (* p q))) (∧ (= (real_pow x (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0)))) (∧ (= (real_pow x (NUMERAL (BIT1 _0))) x) (∧ (= (real_mul x (real_add y z)) (real_add (real_mul x y) (real_mul x z))) (= (real_pow x (SUC q)) (real_mul x (real_pow x q)))))))));
