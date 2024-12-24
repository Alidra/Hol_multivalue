require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7936917 [A] (s : El (fun A bool)) (n : El num) : Prf (= T (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex A) s) (NUMERAL n))));
