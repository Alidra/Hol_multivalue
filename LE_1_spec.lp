require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem99082 : Prf (∧ (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (< (NUMERAL _0) n)))) (∧ (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (<= (NUMERAL (BIT1 _0)) n)))) (∧ (∀ (λ n : El num, (⇒ (< (NUMERAL _0) n) (¬ (= n (NUMERAL _0)))))) (∧ (∀ (λ n : El num, (⇒ (< (NUMERAL _0) n) (<= (NUMERAL (BIT1 _0)) n)))) (∧ (∀ (λ n : El num, (⇒ (<= (NUMERAL (BIT1 _0)) n) (< (NUMERAL _0) n)))) (∀ (λ n : El num, (⇒ (<= (NUMERAL (BIT1 _0)) n) (¬ (= n (NUMERAL _0)))))))))));
