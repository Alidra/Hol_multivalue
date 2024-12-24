require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4887421 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ u : El (fun (fun A bool) bool), (⇒ (∧ ((@FINITE (fun A bool)) u) (∀ (λ s : El (fun A bool), (⇒ ((@IN (fun A bool)) s u) ((@INTERSECTION_OF A) (@FINITE (fun A bool)) P s))))) ((@INTERSECTION_OF A) (@FINITE (fun A bool)) P ((@INTERS A) u)))))));
