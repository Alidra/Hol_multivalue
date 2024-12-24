require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6003902 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ p : El (fun A A), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN A) (p x) s)))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (p x) (p y)))) (= x y)))))))) (= ((@iterate B A) op s ((@o A A B) f p)) ((@iterate B A) op s f))))))))))));
