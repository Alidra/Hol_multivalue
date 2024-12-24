require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4860847 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (= ((@UNION_OF A) (@ARBITRARY A) P s) ((@INTERSECTION_OF A) (@ARBITRARY A) (λ s' : El (fun A bool), (P ((@DIFF A) (@UNIV A) s'))) ((@DIFF A) (@UNIV A) s)))))));
