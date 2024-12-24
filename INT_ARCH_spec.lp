require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2350530 : Prf (∀ (λ x : El int, (∀ (λ d : El int, (⇒ (¬ (= d (int_of_num (NUMERAL _0)))) (∃ (λ c : El int, (int_lt x (int_mul c d)))))))));
