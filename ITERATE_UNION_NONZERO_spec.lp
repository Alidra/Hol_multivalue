require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6007453 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE A) t) (∀ (λ x : El A, (⇒ ((@IN A) x ((@INTER A) s t)) (= (f x) ((@neutral B) op))))))) (= ((@iterate B A) op ((@UNION A) s t) f) (op ((@iterate B A) op s f) ((@iterate B A) op t f)))))))))))));
