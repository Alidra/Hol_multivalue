require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem169651 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ q : El num, (∀ (λ r : El num, (⇒ (∧ (= m (+ (* q n) r)) (< r n)) (∧ (= (DIV m n) q) (= (MOD m n) r)))))))))));
