require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307555 : Prf (∀ (λ x : El int, (= (int_le (int_of_num (NUMERAL _0)) x) (∃ (λ y : El real, (= (real_pow y (NUMERAL (BIT0 (BIT1 _0)))) (real_of_int x)))))));
