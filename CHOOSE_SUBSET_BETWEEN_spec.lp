require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4106042 [A] : Prf (∀ (λ n : El num, (∀ (λ s : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∧ ((@SUBSET A) s u) (∧ ((@FINITE A) s) (∧ (<= ((@CARD A) s) n) (⇒ ((@FINITE A) u) (<= n ((@CARD A) u)))))) (∃ (λ t : El (fun A bool), (∧ ((@SUBSET A) s t) (∧ ((@SUBSET A) t u) ((@HAS_SIZE A) t n))))))))))));
