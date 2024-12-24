require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 a3 ≔ (∧ (∀ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (y0 y3) y3)))))) (y0 y1)))))) (∧ (∀ (λ y0 : El (type919 a1), (∀ (λ y1 : El a1, (= ((@GSPEC a1) (λ y2 : El a1, (y0 ((@SETSPEC a1) y2))) y1) (y0 (λ y2 : El bool, (λ y3 : El a1, (∧ y2 (= y1 y3)))))))))) (∧ (∀ (λ y0 : El (fun a2 bool), (∀ (λ y1 : El a2, (= ((@GSPEC a2) (λ y2 : El a2, (∃ (λ y3 : El a2, ((@SETSPEC a2) y2 (y0 y3) y3)))) y1) (y0 y1)))))) (∀ (λ y0 : El (fun a3 bool), (∀ (λ y1 : El a3, (= ((@IN a3) y1 (λ y2 : El a3, (y0 y2))) (y0 y1)))))))));
