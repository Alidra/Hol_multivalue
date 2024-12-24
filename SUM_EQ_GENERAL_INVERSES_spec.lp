require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7178548 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A real), (∀ (λ g : El (fun B real), (∀ (λ h : El (fun A B), (∀ (λ k : El (fun B A), (⇒ (∧ (∀ (λ y : El B, (⇒ ((@IN B) y t) (∧ ((@IN A) (k y) s) (= (h (k y)) y))))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (h x) t) (∧ (= (k (h x)) x) (= (g (h x)) (f x)))))))) (= ((@sum A) s f) ((@sum B) t g)))))))))))))));
