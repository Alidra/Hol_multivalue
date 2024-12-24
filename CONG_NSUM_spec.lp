require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7058518 [A] : Prf (∀ (λ n : El num, (∀ (λ f : El (fun A num), (∀ (λ g : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@== num) (f x) (g x) (num_mod n)))))) ((@== num) ((@nsum A) s f) ((@nsum A) s g) (num_mod n)))))))))));
