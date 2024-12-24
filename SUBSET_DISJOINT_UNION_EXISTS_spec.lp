require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4475749 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ u : El (fun (prod K A) bool), (= ((@SUBSET (prod K A)) u ((@disjoint_union A K) k s)) (∃ (λ t : El (fun K (fun A bool)), (∧ (= u ((@disjoint_union A K) k t)) (∀ (λ i : El K, (⇒ ((@IN K) i k) ((@SUBSET A) (t i) (s i)))))))))))))));
