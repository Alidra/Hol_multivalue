require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1709542 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) y) (real_lt x (real_of_num (NUMERAL (BIT1 _0))))) (∃ (λ n : El num, (real_lt (real_pow x n) y))))))));
