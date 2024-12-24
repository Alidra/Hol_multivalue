require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem523725 (n : El num) : Prf (= ((λ n' : El num, (= (EVEN (BIT0 n')) T)) n) (= (EVEN (BIT0 n)) T));
