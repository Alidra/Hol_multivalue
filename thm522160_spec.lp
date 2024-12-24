require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522160 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (- m (SUC n')) (PRE (- m n')))) n);
