require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8027156 [A M N] : Prf (∀ (λ s : El (fun (cart A M) bool), (∀ (λ t : El (fun (cart A N) bool), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE (cart A M)) s m) ((@HAS_SIZE (cart A N)) t n)) ((@HAS_SIZE (cart A (finite_sum M N))) ((@PCROSS A M N) s t) (* m n)))))))))));
