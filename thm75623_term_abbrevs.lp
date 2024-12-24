require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El (fun num bool)) ≔ (⇒ (∧ (x0 (NUMERAL _0)) (∀ (λ y0 : El num, (⇒ (x0 y0) (x0 (SUC y0)))))) (∀ (λ y0 : El num, (x0 y0))));
symbol term0 (x0: El (fun num bool)) ≔ ((λ y0 : El (fun num bool), (⇒ (∧ (y0 (NUMERAL _0)) (∀ (λ y1 : El num, (⇒ (y0 y1) (y0 (SUC y1)))))) (∀ (λ y1 : El num, (y0 y1))))) x0);
