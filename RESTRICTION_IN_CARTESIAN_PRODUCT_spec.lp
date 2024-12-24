require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4405001 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (∀ (λ f : El (fun K A), (= ((@IN (fun K A)) ((@RESTRICTION K A) k f) ((@cartesian_product A K) k s)) (∀ (λ i : El K, (⇒ ((@IN K) i k) ((@IN A) (f i) (s i))))))))))));
