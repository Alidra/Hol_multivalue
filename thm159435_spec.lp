require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem159435 (m : El num) (n : El num) (h1 : Prf (= n (NUMERAL _0))) : Prf (= (+ (* n (DIV m n)) (MOD m n)) m);
