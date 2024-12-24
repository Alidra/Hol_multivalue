require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem146697 : Prf (∀ (λ n : El num, (∀ (λ x : El num, (= (< (NUMERAL _0) (EXP x n)) (∨ (¬ (= x (NUMERAL _0))) (= n (NUMERAL _0))))))));
