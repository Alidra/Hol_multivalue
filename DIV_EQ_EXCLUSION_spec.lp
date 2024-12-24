require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem218367 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ c : El num, (∀ (λ d : El num, (⇒ (∧ (< (* b c) (* (+ a (NUMERAL (BIT1 _0))) d)) (< (* a d) (* (+ c (NUMERAL (BIT1 _0))) b))) (= (DIV a b) (DIV c d)))))))))));
