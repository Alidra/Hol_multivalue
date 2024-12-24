require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416545 (lx : El int) (rx : El int) (ly : El int) : Prf (= (int_mul (int_mul lx ly) rx) (int_mul (int_mul lx rx) ly));
