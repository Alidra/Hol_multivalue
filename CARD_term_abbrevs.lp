require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (= ((@CARD a0) y0) ((@ITSET num a0) (λ y1 : El a0, (λ y2 : El num, (SUC y2))) y0 (NUMERAL _0)))) x0);
symbol term1 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), ((@ITSET num a0) (λ y1 : El a0, (λ y2 : El num, (SUC y2))) y0 (NUMERAL _0))) x0);
symbol term3 a0 ≔ (∀ (λ y0 : El (fun a0 bool), (= ((@CARD a0) y0) ((@ITSET num a0) (λ y1 : El a0, (λ y2 : El num, (SUC y2))) y0 (NUMERAL _0)))));
symbol term2 a0 (x0: El (fun a0 bool)) ≔ ((@ITSET num a0) (λ y0 : El a0, (λ y1 : El num, (SUC y1))) x0 (NUMERAL _0));
symbol term0 a0 ≔ (λ y0 : El (fun a0 bool), ((@ITSET num a0) (λ y1 : El a0, (λ y2 : El num, (SUC y2))) y0 (NUMERAL _0)));
