require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4887037 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ u : El (fun (fun A bool) bool), (⇒ (∧ ((@FINITE (fun A bool)) u) (∀ (λ s : El (fun A bool), (⇒ ((@IN (fun A bool)) s u) ((@UNION_OF A) (@FINITE (fun A bool)) P s))))) ((@UNION_OF A) (@FINITE (fun A bool)) P ((@UNIONS A) u)))))));
