require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 (x0: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 ((@GSPEC a0) (λ y1 : El a0, (∃ (λ y2 : El a0, ((@SETSPEC a0) y1 (x0 y2) y2)))))) (x0 y0))));
symbol term1 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (y0 y3) y3)))))) (y0 y1))))) x0);
symbol term3 a0 (x0: El (fun a0 bool)) (x1: El a0) ≔ ((λ y0 : El a0, (= ((@IN a0) y0 ((@GSPEC a0) (λ y1 : El a0, (∃ (λ y2 : El a0, ((@SETSPEC a0) y1 (x0 y2) y2)))))) (x0 y0))) x1);
symbol term0 a0 ≔ (∀ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (y0 y3) y3)))))) (y0 y1))))));
