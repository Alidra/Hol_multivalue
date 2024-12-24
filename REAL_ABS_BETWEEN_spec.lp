require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1539149 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ d : El real, (= (∧ (real_lt (real_of_num (NUMERAL _0)) d) (∧ (real_lt (real_sub x d) y) (real_lt y (real_add x d)))) (real_lt (real_abs (real_sub y x)) d))))))));
