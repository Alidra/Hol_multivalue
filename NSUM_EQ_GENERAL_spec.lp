require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7018205 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A num), (∀ (λ g : El (fun B num), (∀ (λ h : El (fun A B), (⇒ (∧ (∀ (λ y : El B, (⇒ ((@IN B) y t) ((@∃! A) (λ x : El A, (∧ ((@IN A) x s) (= (h x) y))))))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (h x) t) (= (g (h x)) (f x))))))) (= ((@nsum A) s f) ((@nsum B) t g)))))))))))));
