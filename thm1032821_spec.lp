require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1032821 (m : El num) (n : El num) (P : El (fun num (fun num bool))) : Prf (= (P (DIV m n) (MOD m n)) (∀ (λ q : El num, (∀ (λ r : El num, (∨ (∧ (∨ (¬ (= n (NUMERAL _0))) (∨ (¬ (= q (NUMERAL _0))) (¬ (= r m)))) (∨ (¬ (= m (+ (* q n) r))) (¬ (< r n)))) (P q r)))))));
