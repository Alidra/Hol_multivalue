require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1008952 (m : El num) (p : El num) : Prf (= (= (EXP m (NUMERAL (BIT0 (BIT1 _0)))) p) (= (* (NUMERAL m) (NUMERAL m)) (NUMERAL p)));
