require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4839941 [A] : Prf (∀ (λ u : El (fun (fun A bool) bool), (∀ (λ v : El (fun (fun A bool) bool), (⇒ (∧ ((@pairwise (fun A bool)) (@DISJOINT A) v) ((@PSUBSET (fun A bool)) u ((@DELETE (fun A bool)) v (@EMPTY A)))) ((@PSUBSET A) ((@UNIONS A) u) ((@UNIONS A) v)))))));
