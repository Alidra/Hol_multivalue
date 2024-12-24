require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7178400 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A real), (∀ (λ g : El (fun B real), (∀ (λ h : El (fun A B), (⇒ (∧ (∀ (λ y : El B, (⇒ ((@IN B) y t) ((@∃! A) (λ x : El A, (∧ ((@IN A) x s) (= (h x) y))))))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (h x) t) (= (g (h x)) (f x))))))) (= ((@sum A) s f) ((@sum B) t g)))))))))))));
