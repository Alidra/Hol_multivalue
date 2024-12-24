require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem161352 (n : El num) (m : El num) : Prf (= (+ (* n (DIV m n)) (MOD m n)) m);
