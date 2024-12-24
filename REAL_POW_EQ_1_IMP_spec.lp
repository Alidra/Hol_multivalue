require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1653669 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (⇒ (∧ (¬ (= n (NUMERAL _0))) (= (real_pow x n) (real_of_num (NUMERAL (BIT1 _0))))) (= (real_abs x) (real_of_num (NUMERAL (BIT1 _0)))))))));
