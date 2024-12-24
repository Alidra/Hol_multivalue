require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (finite_sum a0 a0)) (x1: El (finite_sum a0 a0)) ≔ ((λ y0 : El (finite_sum a0 a0), (= (= ((@mktybit0 a0) x0) ((@mktybit0 a0) y0)) (= x0 y0))) x1);
