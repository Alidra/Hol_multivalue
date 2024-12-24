require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (fun a1 bool)) (x1: El (type1470 a0 a1)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 ((@UNIONS a0) ((@GSPEC (fun a0 bool)) (λ y1 : El (fun a0 bool), (∃ (λ y2 : El a1, ((@SETSPEC (fun a0 bool)) y1 (x0 y2) (x1 y2)))))))) ((@IN a0) y0 ((@GSPEC a0) (λ y1 : El a0, (∃ (λ y2 : El a0, ((@SETSPEC a0) y1 (∃ (λ y3 : El a1, (∧ (x0 y3) ((@IN a0) y2 (x1 y3))))) y2)))))))));
