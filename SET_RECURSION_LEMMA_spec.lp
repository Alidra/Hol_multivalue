require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3814895 [A B] : Prf (∀ (λ f : El (fun A (fun B B)), (∀ (λ b : El B, (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El B, (⇒ (¬ (= x y)) (= (f x (f y s)) (f y (f x s)))))))))) (∃ (λ g : El (fun (fun A bool) B), (∧ (= (g (@EMPTY A)) b) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= (g ((@INSERT A) x s)) ((@COND B) ((@IN A) x s) (g s) (f x (g s)))))))))))))))));
