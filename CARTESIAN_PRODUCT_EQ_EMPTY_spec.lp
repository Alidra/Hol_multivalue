require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4408929 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= (= ((@cartesian_product A K) k s) (@EMPTY (fun K A))) (∃ (λ i : El K, (∧ ((@IN K) i k) (= (s i) (@EMPTY A))))))))));
