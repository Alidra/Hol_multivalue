require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 a0 (x0: El (fun a0 bool)) (x1: El a0) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) x1 ((@DELETE a0) x0 y0)) (∧ ((@IN a0) x1 x0) (¬ (= x1 y0))))));
symbol term2 a0 (x0: El (fun a0 bool)) (x1: El a0) ≔ ((λ y0 : El a0, (∀ (λ y1 : El a0, (= ((@IN a0) y0 ((@DELETE a0) x0 y1)) (∧ ((@IN a0) y0 x0) (¬ (= y0 y1))))))) x1);
symbol term4 a0 (x0: El (fun a0 bool)) (x1: El a0) (x2: El a0) ≔ ((λ y0 : El a0, (= ((@IN a0) x1 ((@DELETE a0) x0 y0)) (∧ ((@IN a0) x1 x0) (¬ (= x1 y0))))) x2);
symbol term1 a0 (x0: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El a0, (= ((@IN a0) y0 ((@DELETE a0) x0 y1)) (∧ ((@IN a0) y0 x0) (¬ (= y0 y1))))))));
symbol term0 a0 (x0: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (= ((@IN a0) y1 ((@DELETE a0) y0 y2)) (∧ ((@IN a0) y1 y0) (¬ (= y1 y2))))))))) x0);
