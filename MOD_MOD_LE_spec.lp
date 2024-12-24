require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem184094 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (∧ (¬ (= n (NUMERAL _0))) (<= n p)) (= (MOD (MOD m n) p) (MOD m n)))))))));
