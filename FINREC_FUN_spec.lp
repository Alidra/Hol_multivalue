require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3812781 [A B] : Prf (∀ (λ f : El (fun A (fun B B)), (∀ (λ b : El B, (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El B, (⇒ (¬ (= x y)) (= (f x (f y s)) (f y (f x s)))))))))) (∃ (λ g : El (fun (fun A bool) B), (∧ (= (g (@EMPTY A)) b) (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (⇒ (∧ ((@FINITE A) s) ((@IN A) x s)) (= (g s) (f x (g ((@DELETE A) s x)))))))))))))))));
