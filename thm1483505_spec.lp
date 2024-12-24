require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483505 (y : El real) (z : El real) (x : El real) (q : El num) : Prf (∧ (= (real_mul x (real_add y z)) (real_add (real_mul x y) (real_mul x z))) (= (real_pow x (SUC q)) (real_mul x (real_pow x q))));
