require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4386843 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ x : El A, (⇒ ((@IN A) x s) (= ((@RESTRICTION A B) s f x) (f x)))))))));
