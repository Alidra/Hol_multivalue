require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4406347 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= ((@cartesian_product A K) k s) ((@GSPEC (fun K A)) (λ GEN_PVAR_142 : El (fun K A), (∃ (λ f : El (fun K A), ((@SETSPEC (fun K A)) GEN_PVAR_142 (∀ (λ i : El K, (⇒ ((@IN K) i k) ((@IN A) (f i) (s i))))) ((@RESTRICTION K A) k f)))))))))));
