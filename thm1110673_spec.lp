require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1110673 [A] (r : El (fun A (fun A bool))) : Prf (= ((λ r' : El (fun A (fun A bool)), (= ((@PAIRWISE A) r' (@NIL A)) T)) r) (= ((@PAIRWISE A) r (@NIL A)) T));
