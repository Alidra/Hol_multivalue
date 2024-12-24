require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem12782 : Prf (∀ (λ b : El bool, (∀ (λ t1 : El bool, (∀ (λ t2 : El bool, (= ((@COND bool) b t1 t2) (∧ (∨ (¬ b) t1) (∨ b t2)))))))));
