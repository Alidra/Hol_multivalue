require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6958318 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∃ (λ x : El A, (∧ ((@IN A) x s) (< (NUMERAL _0) (f x)))))) (< (NUMERAL _0) ((@nsum A) s f)))))));
