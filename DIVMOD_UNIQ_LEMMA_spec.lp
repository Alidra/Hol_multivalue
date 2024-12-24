require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem169424 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ q1 : El num, (∀ (λ r1 : El num, (∀ (λ q2 : El num, (∀ (λ r2 : El num, (⇒ (∧ (∧ (= m (+ (* q1 n) r1)) (< r1 n)) (∧ (= m (+ (* q2 n) r2)) (< r2 n))) (∧ (= q1 q2) (= r1 r2)))))))))))))));
