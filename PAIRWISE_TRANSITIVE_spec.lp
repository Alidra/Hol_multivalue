require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1236911 [A] : Prf (∀ (λ R : El (fun A (fun A bool)), (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ l : El (list A), (⇒ (∀ (λ x' : El A, (∀ (λ y' : El A, (∀ (λ z : El A, (⇒ (∧ (R x' y') (R y' z)) (R x' z)))))))) (= ((@PAIRWISE A) R ((@CONS A) x ((@CONS A) y l))) (∧ (R x y) ((@PAIRWISE A) R ((@CONS A) y l)))))))))))));
