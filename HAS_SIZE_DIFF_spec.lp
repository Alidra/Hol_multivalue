require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3868414 [_100233] : Prf (∀ (λ s : El (fun _100233 bool), (∀ (λ t : El (fun _100233 bool), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE _100233) s m) (∧ ((@HAS_SIZE _100233) t n) ((@SUBSET _100233) t s))) ((@HAS_SIZE _100233) ((@DIFF _100233) s t) (- m n)))))))))));
