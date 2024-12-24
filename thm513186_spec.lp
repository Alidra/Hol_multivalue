require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513186 (n : El num) : Prf (= ((λ n' : El num, (= (PRE (SUC n')) n')) n) (= (PRE (SUC n)) n));
