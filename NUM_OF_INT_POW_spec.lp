require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2835824 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (⇒ (int_le (int_of_num (NUMERAL _0)) x) (= (num_of_int (int_pow x n)) (EXP (num_of_int x) n)))))));
