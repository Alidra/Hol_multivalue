require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem53 [A] : Prf (= (@∃ A) (λ P : El (fun A bool), (∀ (λ q : El bool, (⇒ (∀ (λ x : El A, (⇒ (P x) q))) q)))));
