require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El (fun int bool)) ≔ ((λ y0 : El (fun int bool), (= (∀ (λ y1 : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) y1) (y0 y1)))) (∀ (λ y1 : El num, (y0 (int_of_num y1)))))) x0);
