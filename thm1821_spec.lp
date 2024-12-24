require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1821 (t : El bool) : Prf (∧ (= (⇒ t T) T) (∧ (= (⇒ F t) T) (∧ (= (⇒ t t) T) (= (⇒ t F) (¬ t)))));
