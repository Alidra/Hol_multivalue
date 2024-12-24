require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem209601 : Prf (∧ (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (DIV (+ (* a n) b) n) (+ a (DIV b n)))))))))) (∧ (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (DIV (+ (* n a) b) n) (+ a (DIV b n)))))))))) (∧ (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (DIV (+ b (* a n)) n) (+ (DIV b n) a))))))))) (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (DIV (+ b (* n a)) n) (+ (DIV b n) a))))))))))));
