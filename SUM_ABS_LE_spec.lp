require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7083952 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ g : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (real_abs (f x)) (g x)))))) (real_le (real_abs ((@sum A) s f)) ((@sum A) s g)))))))));
