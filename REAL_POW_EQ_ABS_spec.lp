require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1653544 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (¬ (= n (NUMERAL _0))) (= (real_pow x n) (real_pow y n))) (= (real_abs x) (real_abs y)))))))));
