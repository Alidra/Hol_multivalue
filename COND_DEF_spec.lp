require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem12296 [A] : Prf (= (@COND A) (λ t : El bool, (λ t1 : El A, (λ t2 : El A, ((@ε A) (λ x : El A, (∧ (⇒ (= t T) (= x t1)) (⇒ (= t F) (= x t2)))))))));
