require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20453 (x : El bool) (x1 : El bool) (x0 : El bool) (b : El bool) (h1 : Prf (= b F)) : Prf (= (⇒ (∧ (⇒ (= F F) (= x x0)) (⇒ (= F T) (= x x1))) (= x (∧ (∨ (¬ F) x1) (∨ F x0)))) (⇒ (∧ (⇒ (= b F) (= x x0)) (⇒ (= b T) (= x x1))) (= x (∧ (∨ (¬ b) x1) (∨ b x0)))));
