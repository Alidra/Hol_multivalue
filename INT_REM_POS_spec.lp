require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2394837 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (⇒ (¬ (= b (int_of_num (NUMERAL _0)))) (int_le (int_of_num (NUMERAL _0)) (rem a b)))))));
