require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4797007 [A] : Prf (∀ (λ P : El (fun A (fun A bool)), (∀ (λ Q : El (fun A (fun A bool)), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@pairwise A) P s) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (∧ (P x y) (¬ (= x y))))) (Q x y))))))) ((@pairwise A) Q s))))))));
