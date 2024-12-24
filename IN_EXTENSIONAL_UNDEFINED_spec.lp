require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4383142 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ x : El A, (⇒ (∧ ((@IN (fun A B)) f ((@EXTENSIONAL A B) s)) (¬ ((@IN A) x s))) (= (f x) (@ARB B)))))))));
