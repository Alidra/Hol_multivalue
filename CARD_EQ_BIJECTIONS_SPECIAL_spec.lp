require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5092652 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ a : El A, (∀ (λ b : El B, (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE B) t) (∧ (= ((@CARD A) s) ((@CARD B) t)) (∧ ((@IN A) a s) ((@IN B) b t))))) (∃ (λ f : El (fun A B), (∃ (λ g : El (fun B A), (∧ (= (f a) b) (∧ (= (g b) a) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN B) (f x) t) (= (g (f x)) x))))) (∀ (λ y : El B, (⇒ ((@IN B) y t) (∧ ((@IN A) (g y) s) (= (f (g y)) y)))))))))))))))))))));
