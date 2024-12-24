require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3116350 (n : El num) (m : El num) : Prf (= ((λ n' : El num, (= (= m n') (∧ (num_divides m n') (num_divides n' m)))) n) (= (= m n) (∧ (num_divides m n) (num_divides n m))));
