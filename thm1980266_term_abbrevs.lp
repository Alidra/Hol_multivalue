require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) ≔ ((λ y0 : El real, (= (real_gt y0 x0) (real_lt x0 y0))) x1);
