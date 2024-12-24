require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem120109 : Prf (∀ (λ P : El (fun num (fun num bool)), (⇒ (∧ (∀ (λ m : El num, (P m m))) (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (<= m n) (P m n)) (P m (SUC n)))))))) (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (P m n)))))))));
