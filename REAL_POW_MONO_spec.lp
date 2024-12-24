require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1637789 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ x : El real, (⇒ (∧ (real_le (real_of_num (NUMERAL (BIT1 _0))) x) (<= m n)) (real_le (real_pow x m) (real_pow x n)))))))));
