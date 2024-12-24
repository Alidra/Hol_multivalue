require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1046586 [A B C] : Prf (∀ (λ P : El (fun A (fun B C)), (⇒ (∀ (λ x1 : El A, (∀ (λ y1 : El B, (∀ (λ x2 : El A, (∀ (λ y2 : El B, (= (= (P x1 y1) (P x2 y2)) (∧ (= x1 x2) (= y1 y2))))))))))) (∃ (λ X : El (fun C A), (∃ (λ Y : El (fun C B), (∀ (λ x : El A, (∀ (λ y : El B, (∧ (= (X (P x y)) x) (= (Y (P x y)) y)))))))))))));
