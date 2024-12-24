require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem310011 (t1 : El bool) (t2 : El bool) : Prf (= ((λ t2' : El bool, (= (¬ (⇒ t1 t2')) (∧ t1 (¬ t2')))) t2) (= (¬ (⇒ t1 t2)) (∧ t1 (¬ t2))));
