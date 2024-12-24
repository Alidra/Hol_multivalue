require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5096180 [A B] (n : El num) : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A B), (∀ (λ g : El (fun B A), (⇒ (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (f x) t) (= (g (f x)) x))))) (∧ (∀ (λ y : El B, (⇒ ((@IN B) y t) (∧ ((@IN A) (g y) s) (= (f (g y)) y))))) ((@HAS_SIZE A) s n))) ((@HAS_SIZE B) t n))))))))));
