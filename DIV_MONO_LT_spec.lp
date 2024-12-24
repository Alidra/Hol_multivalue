require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem195907 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (∧ (¬ (= p (NUMERAL _0))) (<= (+ m p) n)) (< (DIV m p) (DIV n p)))))))));
