require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2403240 : Prf (∀ (λ x : El int, (∀ (λ n : El int, (⇒ (int_lt (int_of_num (NUMERAL _0)) n) (int_lt (rem x n) n))))));
