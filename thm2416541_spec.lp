require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416541 (lx : El int) (ly : El int) (rx : El int) (ry : El int) : Prf (= (int_mul (int_mul lx ly) (int_mul rx ry)) (int_mul lx (int_mul ly (int_mul rx ry))));
