require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem153228 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (= (<= (EXP x n) (EXP y n)) (∨ (<= x y) (= n (NUMERAL _0))))))))));
