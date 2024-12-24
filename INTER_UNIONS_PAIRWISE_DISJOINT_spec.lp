require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4833713 [A] : Prf (∀ (λ s : El (fun (fun A bool) bool), (∀ (λ t : El (fun (fun A bool) bool), (⇒ ((@pairwise (fun A bool)) (@DISJOINT A) ((@UNION (fun A bool)) s t)) (= ((@INTER A) ((@UNIONS A) s) ((@UNIONS A) t)) ((@UNIONS A) ((@INTER (fun A bool)) s t))))))));
