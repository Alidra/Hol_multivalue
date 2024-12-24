require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5103099 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ f : El (fun A B), (∀ (λ g : El (fun B A), (⇒ (∧ (∨ ((@FINITE A) s) ((@FINITE B) t)) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (f x) t) (= (g (f x)) x))))) (∀ (λ y : El B, (⇒ ((@IN B) y t) (∧ ((@IN A) (g y) s) (= (f (g y)) y))))))) (= ((@CARD A) s) ((@CARD B) t)))))))))));
