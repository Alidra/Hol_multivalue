require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483466 (lx : El real) (ly : El real) (rx : El real) (ry : El real) : Prf (= (real_mul (real_mul lx ly) (real_mul rx ry)) (real_mul lx (real_mul ly (real_mul rx ry))));
