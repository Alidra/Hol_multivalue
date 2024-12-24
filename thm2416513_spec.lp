require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416513 (a : El int) (b : El int) (m : El int) : Prf (= (int_add (int_mul a m) (int_mul b m)) (int_mul (int_add a b) m));
