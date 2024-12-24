require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4396253 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (= (= ((@RESTRICTION A B) s f) g) (∧ ((@EXTENSIONAL A B) s g) (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) (g x)))))))))))));
