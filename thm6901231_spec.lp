require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6901231 : Prf (= ((@ε num) (λ x : El num, (∀ (λ y : El num, (∧ (= (* x y) y) (= (* y x) y)))))) (NUMERAL (BIT1 _0)));
