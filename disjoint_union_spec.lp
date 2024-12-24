require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4464464 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ s : El (fun K (fun A bool)), (= ((@disjoint_union A K) k s) ((@GSPEC (prod K A)) (λ GEN_PVAR_143 : El (prod K A), (∃ (λ i : El K, (∃ (λ x : El A, ((@SETSPEC (prod K A)) GEN_PVAR_143 (∧ ((@IN K) i k) ((@IN A) x (s i))) ((@̦‚ K A) i x)))))))))))));
