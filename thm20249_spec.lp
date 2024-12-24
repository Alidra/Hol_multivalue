require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20249 (x : El bool) (x1 : El bool) (x0 : El bool) (b : El bool) (h1 : Prf (= b T)) : Prf (= (⇒ (∧ (⇒ (= T F) (= x x0)) (⇒ (= T T) (= x x1))) (= x (∨ (∧ T x1) (∧ (¬ T) x0)))) (⇒ (∧ (⇒ (= b F) (= x x0)) (⇒ (= b T) (= x x1))) (= x (∨ (∧ b x1) (∧ (¬ b) x0)))));
