require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1694088 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ a : El real, (∀ (λ b : El real, (∀ (λ u : El real, (∀ (λ v : El real, (⇒ (∧ (real_lt a x) (∧ (real_lt x b) (∧ (real_lt a y) (∧ (real_lt y b) (∧ (real_le (real_of_num (NUMERAL _0)) u) (∧ (real_le (real_of_num (NUMERAL _0)) v) (= (real_add u v) (real_of_num (NUMERAL (BIT1 _0)))))))))) (∧ (real_lt a (real_add (real_mul u x) (real_mul v y))) (real_lt (real_add (real_mul u x) (real_mul v y)) b)))))))))))))));
