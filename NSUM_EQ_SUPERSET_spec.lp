require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6990845 [A] (g : El (fun A num)) : Prf (∀ (λ f : El (fun A num), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@FINITE A) t) (∧ ((@SUBSET A) t s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x t) (= (f x) (g x))))) (∀ (λ x : El A, (⇒ (∧ ((@IN A) x s) (¬ ((@IN A) x t))) (= (f x) (NUMERAL _0)))))))) (= ((@nsum A) s f) ((@nsum A) t g)))))))));
