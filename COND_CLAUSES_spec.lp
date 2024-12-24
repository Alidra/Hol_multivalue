require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem12647 [A] : Prf (∀ (λ t1 : El A, (∀ (λ t2 : El A, (∧ (= ((@COND A) T t1 t2) t1) (= ((@COND A) F t1 t2) t2))))));
