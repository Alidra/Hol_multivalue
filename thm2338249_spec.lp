require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338249 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (< n' m) (¬ (<= m n')))) n);
