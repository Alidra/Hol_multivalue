require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7173279 [A] : Prf (∀ (λ u : El (fun A bool), (∀ (λ v : El (fun A bool), (∀ (λ f : El (fun A real), (⇒ (∧ ((@FINITE A) u) (∧ ((@FINITE A) v) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x ((@DIFF A) u v)) (real_le (f x) (real_of_num (NUMERAL _0)))))) (∀ (λ x : El A, (⇒ ((@IN A) x ((@DIFF A) v u)) (real_le (real_of_num (NUMERAL _0)) (f x)))))))) (real_le ((@sum A) u f) ((@sum A) v f)))))))));
