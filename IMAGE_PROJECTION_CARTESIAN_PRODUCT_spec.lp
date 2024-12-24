require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4446959 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ i : El K, (= ((@IMAGE (fun K A) A) (λ x : El (fun K A), (x i)) ((@cartesian_product A K) k s)) ((@COND (fun A bool)) (= ((@cartesian_product A K) k s) (@EMPTY (fun K A))) (@EMPTY A) ((@COND (fun A bool)) ((@IN K) i k) (s i) ((@INSERT A) (@ARB A) (@EMPTY A)))))))))));
