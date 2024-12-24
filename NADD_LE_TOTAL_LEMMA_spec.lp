require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1271824 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (⇒ (¬ (nadd_le x y)) (∀ (λ B : El num, (∃ (λ n : El num, (∧ (¬ (= n (NUMERAL _0))) (< (+ (dest_nadd y n) B) (dest_nadd x n))))))))))));
