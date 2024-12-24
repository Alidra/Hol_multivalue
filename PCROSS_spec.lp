require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8003767 [A M N] : Prf (∀ (λ s : El (fun (cart A M) bool), (∀ (λ t : El (fun (cart A N) bool), (= ((@PCROSS A M N) s t) ((@GSPEC (cart A (finite_sum M N))) (λ GEN_PVAR_361 : El (cart A (finite_sum M N)), (∃ (λ x : El (cart A M), (∃ (λ y : El (cart A N), ((@SETSPEC (cart A (finite_sum M N))) GEN_PVAR_361 (∧ ((@IN (cart A M)) x s) ((@IN (cart A N)) y t)) ((@pastecart A M N) x y)))))))))))));
