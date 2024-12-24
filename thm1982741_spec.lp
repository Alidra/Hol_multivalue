require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1982741 (rx : El real) (lx : El real) (ly : El real) (ry : El real) : Prf (= (real_mul (real_mul lx ly) (real_mul rx ry)) (real_mul rx (real_mul (real_mul lx ly) ry)));
