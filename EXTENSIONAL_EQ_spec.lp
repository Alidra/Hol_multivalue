require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4385509 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (⇒ (∧ ((@IN (fun A B)) f ((@EXTENSIONAL A B) s)) (∧ ((@IN (fun A B)) g ((@EXTENSIONAL A B) s)) (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) (g x))))))) (= f g))))))));
