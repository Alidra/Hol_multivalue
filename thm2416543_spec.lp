require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416543 (rx : El int) (lx : El int) (ly : El int) (ry : El int) : Prf (= (int_mul (int_mul lx ly) (int_mul rx ry)) (int_mul rx (int_mul (int_mul lx ly) ry)));
