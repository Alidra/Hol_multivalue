require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1445 : Prf (∀ (λ t : El bool, (∧ (= (= T t) t) (∧ (= (= t T) t) (∧ (= (= F t) (¬ t)) (= (= t F) (¬ t)))))));
