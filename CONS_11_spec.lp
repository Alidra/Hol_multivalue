require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1113436 [A] : Prf (∀ (λ h1' : El A, (∀ (λ h2' : El A, (∀ (λ t1 : El (list A), (∀ (λ t2 : El (list A), (= (= ((@CONS A) h1' t1) ((@CONS A) h2' t2)) (∧ (= h1' h2') (= t1 t2)))))))))));
