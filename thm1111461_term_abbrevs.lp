require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (fun num a0)) ≔ ((λ y0 : El (fun num a0), (= ((@list_of_seq a0) y0 (NUMERAL _0)) (@NIL a0))) x0);
symbol term1 a0 (x0: El (fun num a0)) ≔ ((@list_of_seq a0) x0 (NUMERAL _0));
