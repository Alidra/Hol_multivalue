require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522195 (n : El num) : Prf ((λ n' : El num, (= (BIT1 n') (SUC (+ n' n')))) n);
