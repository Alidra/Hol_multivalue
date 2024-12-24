require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4403516 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= ((@cartesian_product A K) k s) ((@GSPEC (fun K A)) (λ GEN_PVAR_141 : El (fun K A), (∃ (λ f : El (fun K A), ((@SETSPEC (fun K A)) GEN_PVAR_141 (∀ (λ i : El K, ((@IN A) (f i) ((@COND (fun A bool)) ((@IN K) i k) (s i) ((@INSERT A) (@ARB A) (@EMPTY A)))))) f))))))))));
