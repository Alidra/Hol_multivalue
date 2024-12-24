require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem515692 (n : El num) : Prf (= ((λ n' : El num, (= (BIT0 n') (+ n' n'))) n) (= (BIT0 n) (+ n n)));
