require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516614 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (<= m n') (∨ (= m n') (< m n')))) n);
