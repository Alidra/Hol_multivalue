require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1982792 (x : El real) (y : El real) : Prf (= (real_sub x y) (real_add x (real_mul (real_neg (real_of_num (NUMERAL (BIT1 _0)))) y)));
