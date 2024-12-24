require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1640851 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (¬ (= z (real_of_num (NUMERAL _0)))) (= (real_mul z x) (real_mul z y))) (= x y))))))));
