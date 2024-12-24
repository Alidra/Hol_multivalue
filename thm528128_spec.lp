require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem528128 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (+ (BIT1 m) (BIT0 n')) (BIT1 (+ m n')))) n);
