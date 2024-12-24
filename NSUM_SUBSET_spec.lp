require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7006898 [A] : Prf (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun A bool), (∀ (λ f : El (fun A num), (⇒ (∧ ((@FINITE A) u) (∧ ((@FINITE A) v) (∀ (λ x : El A, (⇒ ((@IN A) x ((@DIFF A) u v)) (= (f x) (NUMERAL _0))))))) (<= ((@nsum A) u f) ((@nsum A) v f)))))))));
