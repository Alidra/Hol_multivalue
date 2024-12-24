require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem302783 (m : El num) (n : El num) : Prf (= (= m n) (= (SUC (+ m m)) (+ (* (NUMERAL (BIT0 (BIT1 _0))) n) (NUMERAL (BIT1 _0)))));
