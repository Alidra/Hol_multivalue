require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4868514 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ u : El (fun (fun A bool) bool), (⇒ (∀ (λ s : El (fun A bool), (⇒ ((@IN (fun A bool)) s u) ((@UNION_OF A) (@ARBITRARY A) P s)))) ((@UNION_OF A) (@ARBITRARY A) P ((@UNIONS A) u)))))));
