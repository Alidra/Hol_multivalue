require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem555 (q : El bool) (p : El bool) : Prf (= (∧ (⇒ (∧ p q) (∧ q p)) (⇒ (∧ q p) (∧ p q))) (= (∧ p q) (∧ q p)));
