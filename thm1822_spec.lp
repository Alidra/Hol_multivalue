require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1822 (t : El bool) : Prf (∧ (= (⇒ F t) T) (∧ (= (⇒ t t) T) (= (⇒ t F) (¬ t))));
