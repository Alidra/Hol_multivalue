require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El (fun a1 bool), (∀ (λ y1 : El (type1470 a0 a1), (= ((@UNIONS a0) ((@GSPEC (fun a0 bool)) (λ y2 : El (fun a0 bool), (∃ (λ y3 : El a1, ((@SETSPEC (fun a0 bool)) y2 (y0 y3) (y1 y3))))))) ((@GSPEC a0) (λ y2 : El a0, (∃ (λ y3 : El a0, ((@SETSPEC a0) y2 (∃ (λ y4 : El a1, (∧ (y0 y4) ((@IN a0) y3 (y1 y4))))) y3))))))))));
