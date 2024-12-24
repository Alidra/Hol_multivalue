require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem216054 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ c : El num, (∀ (λ d : El num, (⇒ (∧ (¬ (= b (NUMERAL _0))) (< (* b c) (* (+ a (NUMERAL (BIT1 _0))) d))) (<= (DIV c d) (DIV a b)))))))))));
