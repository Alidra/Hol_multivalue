require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (= (NUMERAL y0) y0)) x0);
symbol term1 ≔ (BIT0 (NUMERAL _0));
symbol term2 ≔ ((@= num) (BIT0 (NUMERAL _0)));
