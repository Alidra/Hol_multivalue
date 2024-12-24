require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El num) (x1: El num) ≔ (EXP x0 (SUC x1));
symbol term0 (x0: El num) (x1: El num) ≔ ((λ y0 : El num, (= (EXP x0 (SUC y0)) (* x0 (EXP x0 y0)))) x1);
symbol term2 (x0: El num) (x1: El num) ≔ (* x0 (EXP x0 x1));
