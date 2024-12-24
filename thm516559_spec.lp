require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516559 (n : El num) : Prf (= ((λ n' : El num, (= (EVEN (SUC n')) (¬ (EVEN n')))) n) (= (EVEN (SUC n)) (¬ (EVEN n))));
