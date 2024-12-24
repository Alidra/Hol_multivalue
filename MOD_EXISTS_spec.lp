require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem186864 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (∃ (λ q : El num, (= m (* n q)))) ((@COND bool) (= n (NUMERAL _0)) (= m (NUMERAL _0)) (= (MOD m n) (NUMERAL _0))))))));
