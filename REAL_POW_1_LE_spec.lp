require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1636868 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (⇒ (∧ (real_le (real_of_num (NUMERAL _0)) x) (real_le x (real_of_num (NUMERAL (BIT1 _0))))) (real_le (real_pow x n) (real_of_num (NUMERAL (BIT1 _0)))))))));
