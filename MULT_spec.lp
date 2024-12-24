require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem80980 : Prf (∧ (∀ (λ n : El num, (= (* (NUMERAL _0) n) (NUMERAL _0)))) (∀ (λ m : El num, (∀ (λ n : El num, (= (* (SUC m) n) (+ (* m n) n)))))));
