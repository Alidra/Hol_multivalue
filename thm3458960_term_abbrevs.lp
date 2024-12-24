require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 ≔ (∀ (λ y0 : El (type1470 a1 a2), (∀ (λ y1 : El (type1517 a0 a1 a2), (= ((@UNIONS a0) ((@GSPEC (fun a0 bool)) (λ y2 : El (fun a0 bool), (∃ (λ y3 : El a2, (∃ (λ y4 : El a1, ((@SETSPEC (fun a0 bool)) y2 (y0 y3 y4) (y1 y3 y4))))))))) ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (∃ (λ y4 : El a2, (∃ (λ y5 : El a1, (∧ (y0 y4 y5) ((@IN a0) y3 (y1 y4 y5))))))) y3))))))))));
