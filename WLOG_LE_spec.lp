require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem109466 (P : El (fun num (fun num bool))) : Prf (⇒ (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (P m n) (P n m)))))) (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (P m n))))))) (∀ (λ m : El num, (∀ (λ n : El num, (P m n))))));
