require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1009824 (m : El num) (n : El num) (p : El num) (h1 : Prf (= (SUC (+ m n)) p)) : Prf (= (< (NUMERAL n) (NUMERAL p)) T);
