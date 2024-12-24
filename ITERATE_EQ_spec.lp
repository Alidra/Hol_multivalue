require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5985778 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) (g x))))) (= ((@iterate B A) op s f) ((@iterate B A) op s g))))))))))));
