require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4452398 [A K] : Prf (∀ (λ P : El (fun K (fun A bool)), (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= (∀ (λ z : El (fun K A), (∀ (λ i : El K, (⇒ (∧ ((@IN (fun K A)) z ((@cartesian_product A K) k s)) ((@IN K) i k)) (P i (z i))))))) (∨ (= ((@cartesian_product A K) k s) (@EMPTY (fun K A))) (∀ (λ i : El K, (∀ (λ x : El A, (⇒ (∧ ((@IN K) i k) ((@IN A) x (s i))) (P i x))))))))))))));
