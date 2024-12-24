require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4086093 [A] : Prf (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (∀ (λ n : El num, (⇒ (<= n ((@CARD A) s)) (∃ (λ t : El (fun A bool), (∧ ((@SUBSET A) t s) ((@HAS_SIZE A) t n))))))))));
