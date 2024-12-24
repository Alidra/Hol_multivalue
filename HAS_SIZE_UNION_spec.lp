require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3868180 [_100197] : Prf (∀ (λ s : El (fun _100197 bool), (∀ (λ t : El (fun _100197 bool), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE _100197) s m) (∧ ((@HAS_SIZE _100197) t n) ((@DISJOINT _100197) s t))) ((@HAS_SIZE _100197) ((@UNION _100197) s t) (+ m n)))))))))));
