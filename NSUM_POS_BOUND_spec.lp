require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6949047 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ b : El num, (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (<= ((@nsum A) s f) b)) (∀ (λ x : El A, (⇒ ((@IN A) x s) (<= (f x) b)))))))))));
