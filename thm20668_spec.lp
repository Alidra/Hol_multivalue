require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20668 (r : El bool) (p : El bool) (q : El bool) : Prf (∧ (= (∨ p (∨ q r)) (∨ q (∨ p r))) (∧ (= (∨ p p) p) (= (∨ p (∨ p q)) (∨ p q))));
