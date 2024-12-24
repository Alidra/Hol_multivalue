require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) (x2: El a0) ≔ ((λ y0 : El a0, (= ((@IN a0) y0 ((@INTER a0) x0 x1)) (∧ ((@IN a0) y0 x0) ((@IN a0) y0 x1)))) x2);
symbol term2 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@INTER a0) x0 y0)) (∧ ((@IN a0) y1 x0) ((@IN a0) y1 y0)))))) x1);
symbol term0 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (∀ (λ y1 : El (fun a0 bool), (∀ (λ y2 : El a0, (= ((@IN a0) y2 ((@INTER a0) y0 y1)) (∧ ((@IN a0) y2 y0) ((@IN a0) y2 y1)))))))) x0);
symbol term3 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 ((@INTER a0) x0 x1)) (∧ ((@IN a0) y0 x0) ((@IN a0) y0 x1)))));
symbol term1 a0 (x0: El (fun a0 bool)) ≔ (∀ (λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@INTER a0) x0 y0)) (∧ ((@IN a0) y1 x0) ((@IN a0) y1 y0)))))));
