require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4399593 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ x : El (fun K A), (= ((@IN (fun K A)) x ((@cartesian_product A K) k s)) (∧ ((@EXTENSIONAL K A) k x) (∀ (λ i : El K, (⇒ ((@IN K) i k) ((@IN A) (x i) (s i)))))))))))));
