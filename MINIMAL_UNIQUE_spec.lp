require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem274982 : Prf (∀ (λ P : El (fun num bool), (∀ (λ n : El num, (⇒ (∧ (P n) (∀ (λ m : El num, (⇒ (< m n) (¬ (P m)))))) (= (minimal P) n))))));
