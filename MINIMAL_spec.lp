require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem273176 : Prf (∀ (λ P : El (fun num bool), (= (∃ (λ n : El num, (P n))) (∧ (P (minimal P)) (∀ (λ m : El num, (⇒ (< m (minimal P)) (¬ (P m)))))))));
