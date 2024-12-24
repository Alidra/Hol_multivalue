require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem155916 : Prf (∀ (λ m : El num, (∀ (λ n : El num, ((@COND bool) (= n (NUMERAL _0)) (∧ (= (DIV m n) (NUMERAL _0)) (= (MOD m n) m)) (∧ (= m (+ (* (DIV m n) n) (MOD m n))) (< (MOD m n) n)))))));
