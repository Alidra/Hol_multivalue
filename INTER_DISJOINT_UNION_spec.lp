require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4482970 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ t : El (fun K (fun A bool)), (= ((@INTER (prod K A)) ((@disjoint_union A K) k s) ((@disjoint_union A K) k t)) ((@disjoint_union A K) k (λ i : El K, ((@INTER A) (s i) (t i)))))))))));
