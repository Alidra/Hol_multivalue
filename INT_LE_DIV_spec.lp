require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2651667 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (∧ (int_le (int_of_num (NUMERAL _0)) m) (int_le (int_of_num (NUMERAL _0)) n)) (int_le (int_of_num (NUMERAL _0)) (div m n)))))));
