require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5783455 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ R : El (fun B (fun B bool)), (⇒ (∧ (R ((@neutral B) op) ((@neutral B) op)) (∀ (λ x1 : El B, (∀ (λ y1 : El B, (∀ (λ x2 : El B, (∀ (λ y2 : El B, (⇒ (∧ (R x1 x2) (R y1 y2)) (R (op x1 y1) (op x2 y2)))))))))))) (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (R (f x) (g x)))))) (R ((@iterate B A) op s f) ((@iterate B A) op s g)))))))))))))));
