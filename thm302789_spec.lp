require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem302789 (m : El num) (n : El num) : Prf (= (= m n) (= (BIT0 m) (* (NUMERAL (BIT0 (BIT1 _0))) n)));
