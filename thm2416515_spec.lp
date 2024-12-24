require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416515 (a : El int) (m : El int) : Prf (= (int_add (int_mul a m) m) (int_mul (int_add a (int_of_num (NUMERAL (BIT1 _0)))) m));
