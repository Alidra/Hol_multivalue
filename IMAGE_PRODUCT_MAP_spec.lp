require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4463342 [A B K] : Prf (∀ (λ f : El (fun K (fun A B)), (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= ((@IMAGE (fun K A) (fun K B)) ((@product_map A B K) k f) ((@cartesian_product A K) k s)) ((@cartesian_product B K) k (λ i : El K, ((@IMAGE A B) (f i) (s i)))))))))));
