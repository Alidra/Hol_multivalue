require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem941349 (m : El num) (n : El num) : Prf (= (= (EXP m (NUMERAL (BIT0 (BIT1 _0)))) n) (= (EXP (BIT1 m) (NUMERAL (BIT0 (BIT1 _0)))) (BIT1 (BIT0 (+ m n)))));
