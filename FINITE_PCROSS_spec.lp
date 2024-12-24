require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8030149 [A M N] : Prf (∀ (λ s : El (fun (cart A M) bool), (∀ (λ t : El (fun (cart A N) bool), (⇒ (∧ ((@FINITE (cart A M)) s) ((@FINITE (cart A N)) t)) ((@FINITE (cart A (finite_sum M N))) ((@PCROSS A M N) s t)))))));
