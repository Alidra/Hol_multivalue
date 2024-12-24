require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem189310 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= a (NUMERAL _0))) (= (< n (DIV b a)) (<= (* a (+ n (NUMERAL (BIT1 _0)))) b)))))))));
