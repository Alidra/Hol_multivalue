require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4944739 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A B), (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE B) t) (∧ (= ((@CARD A) s) ((@CARD B) t)) ((@SUBSET B) ((@IMAGE A B) f s) t)))) (= (∀ (λ y : El B, (⇒ ((@IN B) y t) (∃ (λ x : El A, (∧ ((@IN A) x s) (= (f x) y))))))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y))))))))))))));
