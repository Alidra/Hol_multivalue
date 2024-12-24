require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516886 (n : El num) : Prf (= ((λ n' : El num, (= (+ n' n') (* (NUMERAL (BIT0 (BIT1 _0))) n'))) n) (= (+ n n) (* (NUMERAL (BIT0 (BIT1 _0))) n)));
