require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20339 (x : El bool) (x1 : El bool) (x0 : El bool) : Prf (⇒ (∧ (⇒ (= T F) (= x x0)) (⇒ (= T T) (= x x1))) (= x (∨ (∧ T x1) (∧ (¬ T) x0))));
