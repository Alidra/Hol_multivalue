require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7073063 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ g : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (f x) (g x))))) (∃ (λ x : El A, (∧ ((@IN A) x s) (real_lt (f x) (g x))))))) (real_lt ((@sum A) s f) ((@sum A) s g)))))))));
