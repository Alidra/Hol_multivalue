require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6962131 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun A bool), (⇒ (∧ ((@SUBSET A) u v) (∀ (λ x : El A, (⇒ (∧ ((@IN A) x v) (¬ ((@IN A) x u))) (= (f x) (NUMERAL _0)))))) (= ((@nsum A) v f) ((@nsum A) u f)))))))));
