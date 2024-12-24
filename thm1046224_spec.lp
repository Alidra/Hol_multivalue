require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1046224 : Prf (∧ (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ c : El num, (∀ (λ d : El num, (= (∧ (¬ (= a b)) (¬ (= c d))) (¬ (= (+ (* a c) (* b d)) (+ (* a d) (* b c))))))))))))) (∀ (λ n : El num, (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ c : El num, (∀ (λ d : El num, (⇒ (¬ (= n (NUMERAL _0))) (⇒ (∧ (= a b) (¬ (= c d))) (¬ (= (+ a (* n c)) (+ b (* n d)))))))))))))))));
