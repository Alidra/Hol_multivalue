require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3816218 [A B] : Prf (∀ (λ f : El (fun A (fun B B)), (∀ (λ b : El B, (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El B, (⇒ (¬ (= x y)) (= (f x (f y s)) (f y (f x s)))))))))) (∧ (= ((@ITSET B A) f (@EMPTY A) b) b) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@ITSET B A) f ((@INSERT A) x s) b) ((@COND B) ((@IN A) x s) ((@ITSET B A) f s b) (f x ((@ITSET B A) f s b)))))))))))))));
