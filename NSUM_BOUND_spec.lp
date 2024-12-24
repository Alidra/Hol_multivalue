require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6970588 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A num), (∀ (λ b : El num, (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (<= (f x) b))))) (<= ((@nsum A) s f) (* ((@CARD A) s) b)))))))));
