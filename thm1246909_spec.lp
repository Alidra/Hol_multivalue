require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1246909 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (<= n' m) (¬ (< m n')))) n) (= (<= n m) (¬ (< m n))));
