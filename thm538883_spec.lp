require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem538883 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (+ (BIT0 m) (BIT0 n')) (BIT0 (+ m n')))) n) (= (+ (BIT0 m) (BIT0 n)) (BIT0 (+ m n))));
