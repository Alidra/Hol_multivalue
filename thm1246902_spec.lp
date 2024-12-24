require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1246902 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (< m n') (∃ (λ d : El num, (= n' (+ m (SUC d))))))) n);
