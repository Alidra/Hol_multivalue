require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21741 (t : El bool) : Prf (∧ (= (= t T) t) (∧ (= (= F t) (¬ t)) (= (= t F) (¬ t))));
