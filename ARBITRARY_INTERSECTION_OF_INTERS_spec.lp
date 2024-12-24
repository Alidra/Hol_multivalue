require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4868861 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ u : El (fun (fun A bool) bool), (⇒ (∀ (λ s : El (fun A bool), (⇒ ((@IN (fun A bool)) s u) ((@INTERSECTION_OF A) (@ARBITRARY A) P s)))) ((@INTERSECTION_OF A) (@ARBITRARY A) P ((@INTERS A) u)))))));
