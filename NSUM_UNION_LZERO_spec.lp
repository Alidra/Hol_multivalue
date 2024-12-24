require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6970185 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun A bool), (⇒ (∧ ((@FINITE A) v) (∀ (λ x : El A, (⇒ (∧ ((@IN A) x u) (¬ ((@IN A) x v))) (= (f x) (NUMERAL _0)))))) (= ((@nsum A) ((@UNION A) u v) f) ((@nsum A) v f)))))))));
