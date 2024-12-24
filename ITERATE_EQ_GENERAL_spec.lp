require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5997003 [A B C] : Prf (∀ (λ op : El (fun C (fun C C)), (⇒ ((@monoidal C) op) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A C), (∀ (λ g : El (fun B C), (∀ (λ h : El (fun A B), (⇒ (∧ (∀ (λ y : El B, (⇒ ((@IN B) y t) ((@∃! A) (λ x : El A, (∧ ((@IN A) x s) (= (h x) y))))))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (h x) t) (= (g (h x)) (f x))))))) (= ((@iterate C A) op s f) ((@iterate C B) op t g))))))))))))))));
