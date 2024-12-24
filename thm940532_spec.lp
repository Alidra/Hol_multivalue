require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem940532 (m : El num) (n : El num) : Prf (= (= (EXP m (NUMERAL (BIT0 (BIT1 _0)))) n) (= (EXP (BIT0 m) (NUMERAL (BIT0 (BIT1 _0)))) (BIT0 (BIT0 n))));
