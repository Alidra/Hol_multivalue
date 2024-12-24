require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem531123 (n : El num) : Prf (= ((λ n' : El num, (= (+ (BIT1 n') _0) (BIT1 n'))) n) (= (+ (BIT1 n) _0) (BIT1 n)));
