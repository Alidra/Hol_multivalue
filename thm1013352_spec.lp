require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1013352 (m : El num) (p : El num) (n : El num) (h1 : Prf (= (SUC (+ m p)) n)) : Prf (= (= (NUMERAL n) (NUMERAL p)) F);
