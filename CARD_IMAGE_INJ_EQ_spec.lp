require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4015146 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN B) (f x) t)))) (∀ (λ y : El B, (⇒ ((@IN B) y t) ((@∃! A) (λ x : El A, (∧ ((@IN A) x s) (= (f x) y))))))))) (= ((@CARD B) t) ((@CARD A) s)))))))));
