require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem160343 (m : El num) (n : El num) (h1 : Prf (¬ (= n (NUMERAL _0)))) : Prf (⇒ (¬ (= (+ (* (DIV m n) n) (MOD m n)) m)) F);
