require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3632103 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@INFINITE A) s) ((@FINITE A) t)) ((@INFINITE A) ((@DIFF A) s t)))))));
