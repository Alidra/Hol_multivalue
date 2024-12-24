require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3606772 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@FINITE A) ((@UNION A) s t)) (∧ ((@FINITE A) s) ((@FINITE A) t)))))));
