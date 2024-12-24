require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem586 (p : El bool) (q : El bool) (r : El bool) : Prf (= (∧ (⇒ (∧ (∧ p q) r) (∧ p (∧ q r))) (⇒ (∧ p (∧ q r)) (∧ (∧ p q) r))) (= (∧ (∧ p q) r) (∧ p (∧ q r))));
