require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9102 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ t : El A, (⇒ (∀ (λ x : El A, (⇒ (= x t) (P x)))) (∃ P))))));
