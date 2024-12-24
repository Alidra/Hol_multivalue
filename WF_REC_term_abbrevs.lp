require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type1402 a0)) ≔ (⇒ ((@WF a0) x0) (∀ (λ y0 : El (type549 a0 a1), (⇒ (∀ (λ y1 : El (fun a0 a1), (∀ (λ y2 : El (fun a0 a1), (∀ (λ y3 : El a0, (⇒ (∀ (λ y4 : El a0, (⇒ (x0 y4 y3) (= (y1 y4) (y2 y4))))) (= (y0 y1 y3) (y0 y2 y3))))))))) (∃ (λ y1 : El (fun a0 a1), (∀ (λ y2 : El a0, (= (y1 y2) (y0 y1 y2))))))))));
