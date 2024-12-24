require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5947359 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ p : El (fun A A), (∀ (λ s : El (fun A bool), (⇒ (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN A) (p x) s)))) (∀ (λ y : El A, (⇒ ((@IN A) y s) ((@∃! A) (λ x : El A, (∧ ((@IN A) x s) (= (p x) y)))))))) (= ((@iterate B A) op s f) ((@iterate B A) op s ((@o A A B) f p)))))))))))));
