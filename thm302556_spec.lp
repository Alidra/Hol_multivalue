require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem302556 (m : El num) (n : El num) (p : El num) : Prf (= ((λ p' : El num, (= (= (* m n) (* m p')) (∨ (= m (NUMERAL _0)) (= n p')))) p) (= (= (* m n) (* m p)) (∨ (= m (NUMERAL _0)) (= n p))));
