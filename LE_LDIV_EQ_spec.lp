require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem189160 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= a (NUMERAL _0))) (= (<= (DIV b a) n) (< b (* a (+ n (NUMERAL (BIT1 _0)))))))))))));
