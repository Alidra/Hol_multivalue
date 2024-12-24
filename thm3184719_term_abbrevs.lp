require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∧ (∀ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (= ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (y0 y3) y3)))) y1) (y0 y1)))))) (∀ (λ y0 : El (fun a1 bool), (∀ (λ y1 : El a1, (= ((@IN a1) y1 (λ y2 : El a1, (y0 y2))) (y0 y1)))))));
