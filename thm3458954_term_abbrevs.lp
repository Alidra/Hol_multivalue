require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 a3 (x0: El (type1517 a1 a2 a3)) ≔ (∀ (λ y0 : El (type1524 a0 a1 a2 a3), (= ((@UNIONS a0) ((@GSPEC (fun a0 bool)) (λ y1 : El (fun a0 bool), (∃ (λ y2 : El a3, (∃ (λ y3 : El a2, (∃ (λ y4 : El a1, ((@SETSPEC (fun a0 bool)) y1 (x0 y2 y3 y4) (y0 y2 y3 y4))))))))))) ((@GSPEC a0) (λ y1 : El a0, (∃ (λ y2 : El a0, ((@SETSPEC a0) y1 (∃ (λ y3 : El a3, (∃ (λ y4 : El a2, (∃ (λ y5 : El a1, (∧ (x0 y3 y4 y5) ((@IN a0) y2 (y0 y3 y4 y5))))))))) y2))))))));
symbol term1 a0 a1 a2 a3 ≔ (∀ (λ y0 : El (type1517 a1 a2 a3), (∀ (λ y1 : El (type1524 a0 a1 a2 a3), (= ((@UNIONS a0) ((@GSPEC (fun a0 bool)) (λ y2 : El (fun a0 bool), (∃ (λ y3 : El a3, (∃ (λ y4 : El a2, (∃ (λ y5 : El a1, ((@SETSPEC (fun a0 bool)) y2 (y0 y3 y4 y5) (y1 y3 y4 y5))))))))))) ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (∃ (λ y4 : El a3, (∃ (λ y5 : El a2, (∃ (λ y6 : El a1, (∧ (y0 y4 y5 y6) ((@IN a0) y3 (y1 y4 y5 y6))))))))) y3))))))))));
