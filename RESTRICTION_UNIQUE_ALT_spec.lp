require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4398338 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (= (= f ((@RESTRICTION A B) s g)) (∧ ((@EXTENSIONAL A B) s f) (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) (g x)))))))))))));
