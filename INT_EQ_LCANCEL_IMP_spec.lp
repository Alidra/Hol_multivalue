require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301668 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (¬ (= z (int_of_num (NUMERAL _0)))) (= (int_mul z x) (int_mul z y))) (= x y))))))));
