require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3811194 [A B C] : Prf (∀ (λ P : El (fun A bool), (∀ (λ R : El (fun A (fun B (fun C bool))), (⇒ (∧ (∀ (λ s : El A, (⇒ (P s) (∃ (λ a : El B, (∃ (λ n : El C, (R s a n)))))))) (∀ (λ n1 : El C, (∀ (λ n2 : El C, (∀ (λ s : El A, (∀ (λ a1 : El B, (∀ (λ a2 : El B, (⇒ (∧ (R s a1 n1) (R s a2 n2)) (∧ (= a1 a2) (= n1 n2)))))))))))))) (∃ (λ f : El (fun A B), (∀ (λ s : El A, (∀ (λ a : El B, (⇒ (P s) (= (∃ (λ n : El C, (R s a n))) (= (f s) a))))))))))))));
