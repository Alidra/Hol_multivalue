require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ ((λ y0 : El num, (= (EVEN (BIT0 y0)) T)) x0);
symbol term1 (x0: El num) ≔ (EVEN (BIT0 x0));
