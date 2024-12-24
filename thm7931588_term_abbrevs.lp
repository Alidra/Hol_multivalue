require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (fun a1 a0)) (x1: El (fun a1 bool)) (x2: El (fun a0 bool)) ≔ (⇒ (∧ (∀ (λ y0 : El a0, (⇒ ((@IN a0) y0 x2) (∃ (λ y1 : El a1, (= (x0 y1) y0)))))) (∀ (λ y0 : El a1, (= ((@IN a0) (x0 y0) x2) ((@IN a1) y0 x1))))) (= ((@IMAGE a1 a0) x0 x1) x2));
symbol term0 a0 a1 (x0: El (fun a1 a0)) (x1: El (fun a1 bool)) (x2: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (⇒ (∧ (∀ (λ y1 : El a0, (⇒ ((@IN a0) y1 y0) (∃ (λ y2 : El a1, (= (x0 y2) y1)))))) (∀ (λ y1 : El a1, (= ((@IN a0) (x0 y1) y0) ((@IN a1) y1 x1))))) (= ((@IMAGE a1 a0) x0 x1) y0))) x2);
