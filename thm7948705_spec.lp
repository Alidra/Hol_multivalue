require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7948705 [A] (s : El (fun A bool)) (n : El num) : Prf (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex A) s) (NUMERAL n)));
