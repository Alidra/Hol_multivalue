require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El (type919 a0), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@GSPEC a0) (λ y2 : El a0, (y0 ((@SETSPEC a0) y2))))) (y0 (λ y2 : El bool, (λ y3 : El a0, (∧ y2 (= y1 y3))))))))));
symbol term1 a0 a1 a2 a3 a4 ≔ (∧ (∀ (λ y0 : El (type919 a0), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@GSPEC a0) (λ y2 : El a0, (y0 ((@SETSPEC a0) y2))))) (y0 (λ y2 : El bool, (λ y3 : El a0, (∧ y2 (= y1 y3)))))))))) (∧ (∀ (λ y0 : El (fun a1 bool), (∀ (λ y1 : El a1, (= ((@IN a1) y1 ((@GSPEC a1) (λ y2 : El a1, (∃ (λ y3 : El a1, ((@SETSPEC a1) y2 (y0 y3) y3)))))) (y0 y1)))))) (∧ (∀ (λ y0 : El (type919 a2), (∀ (λ y1 : El a2, (= ((@GSPEC a2) (λ y2 : El a2, (y0 ((@SETSPEC a2) y2))) y1) (y0 (λ y2 : El bool, (λ y3 : El a2, (∧ y2 (= y1 y3)))))))))) (∧ (∀ (λ y0 : El (fun a3 bool), (∀ (λ y1 : El a3, (= ((@GSPEC a3) (λ y2 : El a3, (∃ (λ y3 : El a3, ((@SETSPEC a3) y2 (y0 y3) y3)))) y1) (y0 y1)))))) (∀ (λ y0 : El (fun a4 bool), (∀ (λ y1 : El a4, (= ((@IN a4) y1 (λ y2 : El a4, (y0 y2))) (y0 y1))))))))));
