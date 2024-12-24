require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7053438 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ n : El num, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= (MOD ((@nsum A) s f) n) (MOD ((@nsum A) s (λ i : El A, (MOD (f i) n))) n)))))))));
