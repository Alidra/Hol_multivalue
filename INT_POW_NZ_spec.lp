require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308850 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (⇒ (¬ (= x (int_of_num (NUMERAL _0)))) (¬ (= (int_pow x n) (int_of_num (NUMERAL _0)))))))));
