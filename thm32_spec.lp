require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem32 (p : El bool) (q : El bool) : Prf (= (∧ (⇒ p q) (⇒ q p)) (= p q));
