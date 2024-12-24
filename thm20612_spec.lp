require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20612 (x : El bool) (x1 : El bool) (x0 : El bool) (b : El bool) (h1 : Prf (= b T)) : Prf (⇒ (∧ (⇒ (= b F) (= x x0)) (⇒ (= b T) (= x x1))) (= x (∧ (∨ (¬ b) x1) (∨ b x0))));
