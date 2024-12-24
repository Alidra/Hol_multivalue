require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4455638 [A K] : Prf (∀ (λ P : El (fun K (fun A bool)), (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= (∃ (λ z : El (fun K A), (∧ ((@IN (fun K A)) z ((@cartesian_product A K) k s)) (∀ (λ i : El K, (⇒ ((@IN K) i k) (P i (z i)))))))) (∀ (λ i : El K, (⇒ ((@IN K) i k) (∃ (λ x : El A, (∧ ((@IN A) x (s i)) (P i x))))))))))))));
