require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5029861 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE B) t) (<= ((@CARD A) s) ((@CARD B) t)))) (∃ (λ f : El (fun A B), (∧ ((@SUBSET B) ((@IMAGE A B) f s) t) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y))))))))))))));
