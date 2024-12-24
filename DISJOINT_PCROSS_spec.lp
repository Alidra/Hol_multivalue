require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8057341 [A M N] : Prf (∀ (λ s : El (fun (cart A M) bool), (∀ (λ t : El (fun (cart A N) bool), (∀ (λ s' : El (fun (cart A M) bool), (∀ (λ t' : El (fun (cart A N) bool), (= ((@DISJOINT (cart A (finite_sum M N))) ((@PCROSS A M N) s t) ((@PCROSS A M N) s' t')) (∨ ((@DISJOINT (cart A M)) s s') ((@DISJOINT (cart A N)) t t')))))))))));
