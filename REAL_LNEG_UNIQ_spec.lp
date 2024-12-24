require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1490175 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (= (real_add x y) (real_of_num (NUMERAL _0))) (= x (real_neg y)))))));
