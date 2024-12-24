require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (list a0)) ≔ ((λ y0 : El (list a0), (= ((@EL a0) (NUMERAL _0) y0) ((@HD a0) y0))) x0);
symbol term1 a0 (x0: El (list a0)) ≔ ((@EL a0) (NUMERAL _0) x0);
