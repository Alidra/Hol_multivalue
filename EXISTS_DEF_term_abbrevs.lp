require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El bool, (⇒ (∀ (λ y2 : El a0, (⇒ (y0 y2) y1))) y1))));
