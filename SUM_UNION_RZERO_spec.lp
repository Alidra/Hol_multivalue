require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7129616 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun A bool), (⇒ (∧ ((@FINITE A) u) (∀ (λ x : El A, (⇒ (∧ ((@IN A) x v) (¬ ((@IN A) x u))) (= (f x) (real_of_num (NUMERAL _0))))))) (= ((@sum A) ((@UNION A) u v) f) ((@sum A) u f)))))))));
