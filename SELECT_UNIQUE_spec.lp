require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9522 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ x : El A, (⇒ (∀ (λ y : El A, (= (P y) (= y x)))) (= ((@ε A) P) x))))));
