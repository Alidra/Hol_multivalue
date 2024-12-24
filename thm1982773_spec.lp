require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1982773 (x : El real) (y : El real) (q : El num) : Prf (= (real_pow (real_mul x y) q) (real_mul (real_pow x q) (real_pow y q)));
