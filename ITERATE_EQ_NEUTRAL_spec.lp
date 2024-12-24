require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5804540 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) ((@neutral B) op))))) (= ((@iterate B A) op s f) ((@neutral B) op))))))))));
