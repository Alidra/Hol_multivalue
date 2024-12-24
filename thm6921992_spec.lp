require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6921992 : Prf (= ((@ε num) (λ x : El num, (∀ (λ y : El num, (∧ (= (+ x y) y) (= (+ y x) y)))))) (NUMERAL _0));
