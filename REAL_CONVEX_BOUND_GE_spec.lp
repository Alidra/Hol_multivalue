require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1685642 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ a : El real, (∀ (λ u : El real, (∀ (λ v : El real, (⇒ (∧ (real_le a x) (∧ (real_le a y) (∧ (real_le (real_of_num (NUMERAL _0)) u) (∧ (real_le (real_of_num (NUMERAL _0)) v) (= (real_add u v) (real_of_num (NUMERAL (BIT1 _0)))))))) (real_le a (real_add (real_mul u x) (real_mul v y))))))))))))));
