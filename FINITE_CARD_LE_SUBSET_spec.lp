require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3908873 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ n : El num, (⇒ (∧ ((@SUBSET A) s t) (∧ ((@FINITE A) t) (<= ((@CARD A) t) n))) (∧ ((@FINITE A) s) (<= ((@CARD A) s) n)))))))));
