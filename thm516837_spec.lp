require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem516837 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (= (* m n') _0) (∨ (= m _0) (= n' _0)))) n) (= (= (* m n) _0) (∨ (= m _0) (= n _0))));
