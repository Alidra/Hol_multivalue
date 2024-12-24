require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (fun a0 a1)) (x1: El (fun a0 bool)) (x2: El num) ≔ (⇒ (∧ (∀ (λ y0 : El a0, (∀ (λ y1 : El a0, (⇒ (∧ ((@IN a0) y0 x1) (∧ ((@IN a0) y1 x1) (= (x0 y0) (x0 y1)))) (= y0 y1)))))) ((@HAS_SIZE a0) x1 x2)) ((@HAS_SIZE a1) ((@IMAGE a0 a1) x0 x1) x2));
symbol term0 a0 a1 (x0: El (fun a0 a1)) (x1: El (fun a0 bool)) (x2: El num) ≔ ((λ y0 : El num, (⇒ (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (⇒ (∧ ((@IN a0) y1 x1) (∧ ((@IN a0) y2 x1) (= (x0 y1) (x0 y2)))) (= y1 y2)))))) ((@HAS_SIZE a0) x1 y0)) ((@HAS_SIZE a1) ((@IMAGE a0 a1) x0 x1) y0))) x2);
