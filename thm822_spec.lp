require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem822 (p : El bool) (q : El bool) : Prf (= (∧ (⇒ (∨ p (∨ p q)) (∨ p q)) (⇒ (∨ p q) (∨ p (∨ p q)))) (= (∨ p (∨ p q)) (∨ p q)));
