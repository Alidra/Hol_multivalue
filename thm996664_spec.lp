require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem996664 (m : El num) (n : El num) (p : El num) : Prf (= (= (* m n) p) (= (* (BIT0 m) n) (BIT0 p)));
