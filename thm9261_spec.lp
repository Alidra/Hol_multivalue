require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9261 [A] : Prf (⇒ (∀ (λ x : El (fun A bool), (= (∃ x) ((λ P : El (fun A bool), (P ((@ε A) P))) x)))) (= (@∃ A) (λ P : El (fun A bool), (P ((@ε A) P)))));
