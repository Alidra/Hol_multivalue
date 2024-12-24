require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1823 (t : El bool) : Prf (∧ (= (⇒ t t) T) (= (⇒ t F) (¬ t)));
