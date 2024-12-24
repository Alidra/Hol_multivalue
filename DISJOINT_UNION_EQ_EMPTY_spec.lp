require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4491919 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= (= ((@disjoint_union A K) k s) (@EMPTY (prod K A))) (∀ (λ i : El K, (⇒ ((@IN K) i k) (= (s i) (@EMPTY A))))))))));
