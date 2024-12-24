require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7637147 [A] (s : El (fun A bool)) : Prf (= ((λ s' : El (fun A bool), (= ((@dimindex A) s') ((@dimindex A) (@UNIV A)))) s) (= ((@dimindex A) s) ((@dimindex A) (@UNIV A))));
