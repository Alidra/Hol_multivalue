require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 x0) ((@IN a0) y0 x1))));
symbol term1 (x0: El (fun num bool)) (x1: El (fun num bool)) ≔ (∀ (λ y0 : El num, (= ((@IN num) y0 x0) ((@IN num) y0 x1))));
symbol term3 ≔ ((@INSERT num) (NUMERAL _0) (@EMPTY num));
symbol term4 (x0: El num) ≔ (∀ (λ y0 : El num, (= ((@IN num) y0 (… x0 (NUMERAL _0))) ((@IN num) y0 ((@INSERT num) (NUMERAL _0) (@EMPTY num))))));
symbol term2 (x0: El num) ≔ (… x0 (NUMERAL _0));
