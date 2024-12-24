require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem715538 (n : El num) : Prf (= ((λ n' : El num, (= (SUC (BIT0 n')) (BIT1 n'))) n) (= (SUC (BIT0 n)) (BIT1 n)));
