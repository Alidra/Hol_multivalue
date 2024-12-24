require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type549 a0 a1)) (x1: El (type1402 a0)) (x2: El (type1413 a0 a1)) ≔ (∧ (∀ (λ y0 : El (fun a0 a1), (∀ (λ y1 : El a0, (⇒ (∀ (λ y2 : El a0, (⇒ (x1 y2 y1) (x2 y2 (y0 y2))))) (x2 y1 (x0 y0 y1))))))) (∧ (∀ (λ y0 : El (type1413 a0 a1), (⇒ (∀ (λ y1 : El (fun a0 a1), (∀ (λ y2 : El a0, (⇒ (∀ (λ y3 : El a0, (⇒ (x1 y3 y2) (y0 y3 (y1 y3))))) (y0 y2 (x0 y1 y2))))))) (∀ (λ y1 : El a0, (∀ (λ y2 : El a1, (⇒ (x2 y1 y2) (y0 y1 y2))))))))) (∀ (λ y0 : El a0, (∀ (λ y1 : El a1, (= (x2 y0 y1) (∃ (λ y2 : El (fun a0 a1), (∧ (= y1 (x0 y2 y0)) (∀ (λ y3 : El a0, (⇒ (x1 y3 y0) (x2 y3 (y2 y3)))))))))))))));
