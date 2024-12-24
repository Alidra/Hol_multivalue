require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 (x0: El (type1470 a1 a2)) (x1: El (type1517 a0 a1 a2)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 ((@INTERS a0) ((@GSPEC (fun a0 bool)) (λ y1 : El (fun a0 bool), (∃ (λ y2 : El a2, (∃ (λ y3 : El a1, ((@SETSPEC (fun a0 bool)) y1 (x0 y2 y3) (x1 y2 y3)))))))))) ((@IN a0) y0 ((@GSPEC a0) (λ y1 : El a0, (∃ (λ y2 : El a0, ((@SETSPEC a0) y1 (∀ (λ y3 : El a2, (∀ (λ y4 : El a1, (⇒ (x0 y3 y4) ((@IN a0) y2 (x1 y3 y4))))))) y2)))))))));
