require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem528241 (n : El num) : Prf (= ((λ n' : El num, (= (+ _0 (BIT1 n')) (BIT1 n'))) n) (= (+ _0 (BIT1 n)) (BIT1 n)));
