require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2657711 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (∧ (int_lt (int_of_num (NUMERAL _0)) n) (int_le n m)) (int_lt (int_of_num (NUMERAL _0)) (div m n)))))));
