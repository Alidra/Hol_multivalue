require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem10299 : Prf (∀ (λ t1 : El bool, (∀ (λ t2 : El bool, (= (¬ (⇒ t1 t2)) (∧ t1 (¬ t2)))))));
