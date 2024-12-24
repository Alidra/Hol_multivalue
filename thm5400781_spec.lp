require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400781 (m : El num) (n : El num) (p : El num) : Prf ((λ p' : El num, (= ((@IN num) p' (… m n)) (∧ (<= m p') (<= p' n)))) p);
