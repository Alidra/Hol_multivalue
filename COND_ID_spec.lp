require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem12860 [A] : Prf (∀ (λ b : El bool, (∀ (λ t : El A, (= ((@COND A) b t t) t)))));
