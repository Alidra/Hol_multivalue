require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1139083 [A] : Prf (∀ (λ n : El num, (∀ (λ x : El A, (∀ (λ y : El A, (= ((@MEM A) x ((@REPLICATE A) n y)) (∧ (= x y) (¬ (= n (NUMERAL _0)))))))))));
