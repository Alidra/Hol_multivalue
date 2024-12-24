require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338244 (t2 : El bool) (t1 : El bool) : Prf (= ((λ t2' : El bool, (= (⇒ (¬ t1) (¬ t2')) (⇒ t2' t1))) t2) (= (⇒ (¬ t1) (¬ t2)) (⇒ t2 t1)));
