require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3743381 [A] : Prf (∀ (λ R : El (fun A (fun A bool)), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (∀ (λ x : El A, (¬ (R x x)))) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ z : El A, (⇒ (∧ (R x y) (R y z)) (R x z)))))))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∃ (λ y : El A, (∧ ((@IN A) y s) (R x y)))))))))) (= s (@EMPTY A)))))));
