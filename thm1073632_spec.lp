require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1073632 [A] : Prf (∀ (λ a0 : El A, (∀ (λ a1 : El (list A), (∀ (λ a0' : El A, (∀ (λ a1' : El (list A), (= (= ((@CONS A) a0 a1) ((@CONS A) a0' a1')) (∧ (= a0 a0') (= a1 a1')))))))))));
