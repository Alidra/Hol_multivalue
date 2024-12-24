require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513174 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (+ (SUC m) n') (SUC (+ m n')))) n) (= (+ (SUC m) n) (SUC (+ m n))));
