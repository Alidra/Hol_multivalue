require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 ≔ (∧ (∀ (λ y0 : El (type919 a0), (∀ (λ y1 : El a0, (= ((@GSPEC a0) (λ y2 : El a0, (y0 ((@SETSPEC a0) y2))) y1) (y0 (λ y2 : El bool, (λ y3 : El a0, (∧ y2 (= y1 y3)))))))))) (∧ (∀ (λ y0 : El (fun a1 bool), (∀ (λ y1 : El a1, (= ((@GSPEC a1) (λ y2 : El a1, (∃ (λ y3 : El a1, ((@SETSPEC a1) y2 (y0 y3) y3)))) y1) (y0 y1)))))) (∀ (λ y0 : El (fun a2 bool), (∀ (λ y1 : El a2, (= ((@IN a2) y1 (λ y2 : El a2, (y0 y2))) (y0 y1))))))));
