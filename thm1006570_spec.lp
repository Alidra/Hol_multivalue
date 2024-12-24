require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1006570 (m : El num) (n : El num) (p : El num) : Prf (= (= (+ m n) p) (= (+ (NUMERAL m) (NUMERAL n)) (NUMERAL p)));
