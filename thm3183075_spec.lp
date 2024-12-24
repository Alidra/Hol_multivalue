require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3183075 [A] (p : El (fun A bool)) : Prf (= ((λ p' : El (fun A bool), (= ((@GSPEC A) p') p')) p) (= ((@GSPEC A) p) p));
