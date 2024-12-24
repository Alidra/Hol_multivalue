require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem273060 : Prf (∀ (λ P : El (fun num bool), (= (minimal P) ((@ε num) (λ n : El num, (∧ (P n) (∀ (λ m : El num, (⇒ (< m n) (¬ (P m)))))))))));
