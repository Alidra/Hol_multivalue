require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (fun a1 bool)) (x1: El (type1470 a0 a1)) ≔ (∀ (λ y0 : El a1, (⇒ (x0 y0) (∀ (λ y1 : El a0, (x1 y0 y1))))));
symbol term0 (x0: El bool) ≔ (⇒ (¬ x0) F);
symbol term2 a0 a1 (x0: El (fun a1 bool)) (x1: El (type1470 a0 a1)) ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El a1, (⇒ (x0 y1) (x1 y1 y0))))));
symbol term3 a0 a1 (x0: El (fun a1 bool)) (x1: El (type1470 a0 a1)) ≔ (⇒ (¬ (= (∀ (λ y0 : El a1, (⇒ (x0 y0) (∀ (λ y1 : El a0, (x1 y0 y1)))))) (∀ (λ y0 : El a0, (∀ (λ y1 : El a1, (⇒ (x0 y1) (x1 y1 y0)))))))) F);
