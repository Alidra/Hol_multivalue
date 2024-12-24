require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7156962 [A] (g : El (fun A real)) : Prf (∀ (λ f : El (fun A real), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@FINITE A) t) (∧ ((@SUBSET A) t s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x t) (= (f x) (g x))))) (∀ (λ x : El A, (⇒ (∧ ((@IN A) x s) (¬ ((@IN A) x t))) (= (f x) (real_of_num (NUMERAL _0))))))))) (= ((@sum A) s f) ((@sum A) t g)))))))));
