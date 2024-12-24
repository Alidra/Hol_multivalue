require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513173 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (+ (SUC m) n') (SUC (+ m n')))) n);
