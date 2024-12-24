require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308223 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (⇒ (int_le (int_of_num (NUMERAL _0)) x) (int_le (int_of_num (NUMERAL _0)) (int_pow x n)))))));
