require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4387092 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ x : El A, (∀ (λ y : El B, (⇒ (∧ ((@IN A) x s) (= (f x) y)) (= ((@RESTRICTION A B) s f x) y))))))))));
