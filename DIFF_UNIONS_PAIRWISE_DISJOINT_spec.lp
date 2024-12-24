require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4829792 [A] : Prf (∀ (λ s : El (fun (fun A bool) bool), (∀ (λ t : El (fun (fun A bool) bool), (⇒ (∧ ((@pairwise (fun A bool)) (@DISJOINT A) s) ((@SUBSET (fun A bool)) t s)) (= ((@DIFF A) ((@UNIONS A) s) ((@UNIONS A) t)) ((@UNIONS A) ((@DIFF (fun A bool)) s t))))))));
