require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4399444 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= ((@cartesian_product A K) k s) ((@GSPEC (fun K A)) (λ GEN_PVAR_140 : El (fun K A), (∃ (λ f : El (fun K A), ((@SETSPEC (fun K A)) GEN_PVAR_140 (∧ ((@EXTENSIONAL K A) k f) (∀ (λ i : El K, (⇒ ((@IN K) i k) ((@IN A) (f i) (s i)))))) f))))))))));
