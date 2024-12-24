require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem531183 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (+ (BIT1 m) (BIT1 n')) (BIT0 (SUC (+ m n'))))) n);
