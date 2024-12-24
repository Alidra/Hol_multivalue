require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6449238 [A K] : Prf (∀ (λ dom : El (fun A bool), (∀ (λ neut : El A, (∀ (λ op : El (fun A (fun A A)), (∀ (λ <<= : El (fun K (fun K bool)), (∀ (λ k : El (fun K bool), (∀ (λ f : El (fun K A), (= ((@iterato A K) dom neut op <<= ((@GSPEC K) (λ GEN_PVAR_268 : El K, (∃ (λ i : El K, ((@SETSPEC K) GEN_PVAR_268 (∧ ((@IN K) i k) ((@IN A) (f i) ((@DIFF A) dom ((@INSERT A) neut (@EMPTY A))))) i))))) f) ((@iterato A K) dom neut op <<= k f))))))))))))));
