require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1246903 (n : El num) (m : El num) : Prf (= ((λ n' : El num, (= (< m n') (∃ (λ d : El num, (= n' (+ m (SUC d))))))) n) (= (< m n) (∃ (λ d : El num, (= n (+ m (SUC d)))))));
