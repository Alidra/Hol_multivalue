require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211739 [A] (s : El (fun A bool)) (t : El (fun A bool)) : Prf (= ((λ t' : El (fun A bool), (= ((@DISJOINT A) s t') (= ((@INTER A) s t') (@EMPTY A)))) t) (= ((@DISJOINT A) s t) (= ((@INTER A) s t) (@EMPTY A))));
