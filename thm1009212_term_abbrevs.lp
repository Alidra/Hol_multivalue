require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 (x0: El num) (x1: El num) ≔ ((@= num) (EXP (NUMERAL x0) (NUMERAL x1)));
symbol term1 (x0: El num) ≔ (EXP (NUMERAL x0));
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (= (NUMERAL y0) y0)) x0);
symbol term4 (x0: El num) (x1: El num) ≔ ((@= num) (EXP x0 x1));
symbol term2 (x0: El num) (x1: El num) ≔ (EXP (NUMERAL x0) (NUMERAL x1));
