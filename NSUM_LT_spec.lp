require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6934233 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ g : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (<= (f x) (g x))))) (∃ (λ x : El A, (∧ ((@IN A) x s) (< (f x) (g x))))))) (< ((@nsum A) s f) ((@nsum A) s g)))))))));
