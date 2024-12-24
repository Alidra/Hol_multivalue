require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem531111 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (+ (BIT0 m) (BIT1 n')) (BIT1 (+ m n')))) n);
