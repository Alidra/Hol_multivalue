require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 a0 (x0: El (type1400 a0)) ≔ (∧ (∀ (λ y0 : El a0, (∀ (λ y1 : El a0, (= (x0 y0 y1) (x0 y1 y0)))))) (∧ (∀ (λ y0 : El a0, (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (= (x0 y0 (x0 y1 y2)) (x0 (x0 y0 y1) y2)))))))) (∀ (λ y0 : El a0, (= (x0 ((@neutral a0) x0) y0) y0)))));
symbol term4 a0 (x0: El (type1400 a0)) ≔ ((λ y0 : El (type1400 a0), (= ((@monoidal a0) y0) (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (= (y0 y1 y2) (y0 y2 y1)))))) (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (∀ (λ y3 : El a0, (= (y0 y1 (y0 y2 y3)) (y0 (y0 y1 y2) y3)))))))) (∀ (λ y1 : El a0, (= (y0 ((@neutral a0) y0) y1) y1))))))) x0);
symbol term0 a0 ≔ (λ y0 : El (type1400 a0), (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (= (y0 y1 y2) (y0 y2 y1)))))) (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (∀ (λ y3 : El a0, (= (y0 y1 (y0 y2 y3)) (y0 (y0 y1 y2) y3)))))))) (∀ (λ y1 : El a0, (= (y0 ((@neutral a0) y0) y1) y1))))));
symbol term1 a0 (x0: El (type1400 a0)) ≔ ((λ y0 : El (type1400 a0), (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (= (y0 y1 y2) (y0 y2 y1)))))) (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (∀ (λ y3 : El a0, (= (y0 y1 (y0 y2 y3)) (y0 (y0 y1 y2) y3)))))))) (∀ (λ y1 : El a0, (= (y0 ((@neutral a0) y0) y1) y1)))))) x0);
symbol term3 a0 ≔ (∀ (λ y0 : El (type1400 a0), (= ((@monoidal a0) y0) (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (= (y0 y1 y2) (y0 y2 y1)))))) (∧ (∀ (λ y1 : El a0, (∀ (λ y2 : El a0, (∀ (λ y3 : El a0, (= (y0 y1 (y0 y2 y3)) (y0 (y0 y1 y2) y3)))))))) (∀ (λ y1 : El a0, (= (y0 ((@neutral a0) y0) y1) y1))))))));
