require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516893 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (<= m (SUC n')) (∨ (= m (SUC n')) (<= m n')))) n) (= (<= m (SUC n)) (∨ (= m (SUC n)) (<= m n))));
