require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1966798 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_le (real_of_num (NUMERAL _0)) x) (∧ (real_le (real_of_num (NUMERAL _0)) y) (real_le x (sqrt y)))) (real_le (real_pow x (NUMERAL (BIT0 (BIT1 _0)))) y))))));
