require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308685 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ x : El int, (⇒ (∧ (int_le (int_of_num (NUMERAL (BIT1 _0))) x) (<= m n)) (int_le (int_pow x m) (int_pow x n)))))))));
