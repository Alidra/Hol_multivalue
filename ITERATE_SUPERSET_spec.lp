require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6016892 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun A bool), (⇒ (∧ ((@SUBSET A) u v) (∀ (λ x : El A, (⇒ (∧ ((@IN A) x v) (¬ ((@IN A) x u))) (= (f x) ((@neutral B) op)))))) (= ((@iterate B A) op v f) ((@iterate B A) op u f))))))))))));
