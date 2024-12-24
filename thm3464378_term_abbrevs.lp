require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (fun a1 bool)) (x1: El (type1470 a0 a1)) ≔ ((@INTERS a0) ((@GSPEC (fun a0 bool)) (λ y0 : El (fun a0 bool), (∃ (λ y1 : El a1, ((@SETSPEC (fun a0 bool)) y0 (x0 y1) (x1 y1)))))));
symbol term1 a0 a1 (x0: El (fun a1 bool)) (x1: El (type1470 a0 a1)) ≔ ((@GSPEC a0) (λ y0 : El a0, (∃ (λ y1 : El a0, ((@SETSPEC a0) y0 (∀ (λ y2 : El a1, (⇒ (x0 y2) ((@IN a0) y1 (x1 y2))))) y1)))));
