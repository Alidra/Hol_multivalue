require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1962247 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_le (real_of_num (NUMERAL _0)) y) (real_lt x (real_pow y (NUMERAL (BIT0 (BIT1 _0)))))) (real_lt (sqrt x) y))))));
