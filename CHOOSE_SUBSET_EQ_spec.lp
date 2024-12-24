require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4085033 [A] : Prf (∀ (λ n : El num, (∀ (λ s : El (fun A bool), (= (⇒ ((@FINITE A) s) (<= n ((@CARD A) s))) (∃ (λ t : El (fun A bool), (∧ ((@SUBSET A) t s) ((@HAS_SIZE A) t n)))))))));
