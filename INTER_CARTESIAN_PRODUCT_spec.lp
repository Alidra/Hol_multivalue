require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4432366 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ t : El (fun K (fun A bool)), (= ((@INTER (fun K A)) ((@cartesian_product A K) k s) ((@cartesian_product A K) k t)) ((@cartesian_product A K) k (λ i : El K, ((@INTER A) (s i) (t i)))))))))));
