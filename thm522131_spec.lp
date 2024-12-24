require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522131 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (¬ (<= m n')) (< n' m))) n);
