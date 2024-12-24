require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem10190 : Prf (= (∀ (λ t : El bool, (= (¬ (¬ t)) t))) (∀ (λ t : El bool, (= (¬ (¬ t)) t))));
