require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4409647 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ x : El (fun K A), (∀ (λ y : El (fun K A), (⇒ (∧ ((@IN (fun K A)) x ((@cartesian_product A K) k s)) (∧ ((@IN (fun K A)) y ((@cartesian_product A K) k s)) (∀ (λ i : El K, (⇒ ((@IN K) i k) (= (x i) (y i))))))) (= x y))))))))));
