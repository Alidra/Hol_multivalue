require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516577 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (EVEN (* m n')) (∨ (EVEN m) (EVEN n')))) n);
