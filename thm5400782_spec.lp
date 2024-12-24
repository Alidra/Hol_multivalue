require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5400782 (m : El num) (p : El num) (n : El num) : Prf (= ((λ p' : El num, (= ((@IN num) p' (… m n)) (∧ (<= m p') (<= p' n)))) p) (= ((@IN num) p (… m n)) (∧ (<= m p) (<= p n))));
