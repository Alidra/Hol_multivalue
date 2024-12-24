require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem135075 : Prf (∧ (∀ (λ m : El num, (= (- m (NUMERAL _0)) m))) (∀ (λ m : El num, (∀ (λ n : El num, (= (- m (SUC n)) (PRE (- m n))))))));
