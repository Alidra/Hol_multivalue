require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5119703 [A] : Prf (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) ((@WF (fun A bool)) (λ t1 : El (fun A bool), (λ t2 : El (fun A bool), (∧ ((@PSUBSET A) t1 t2) ((@SUBSET A) t2 s))))))));
