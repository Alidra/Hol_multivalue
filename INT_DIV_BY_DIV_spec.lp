require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2732856 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (∧ (¬ (= n (int_of_num (NUMERAL _0)))) (int_divides m n)) (= (div n (div n m)) m))))));
