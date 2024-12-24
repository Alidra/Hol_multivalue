require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem616 (p : El bool) (q : El bool) (r : El bool) : Prf (∧ (⇒ (∧ p (∧ q r)) (∧ q (∧ p r))) (⇒ (∧ q (∧ p r)) (∧ p (∧ q r))));
