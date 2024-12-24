require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3197563 [A] : Prf (∧ (∧ ((@FINITE A) (@EMPTY A)) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) ((@FINITE A) ((@INSERT A) x s)))))))) (∧ (∀ (λ FINITE' : El (fun (fun A bool) bool), (⇒ (∧ (FINITE' (@EMPTY A)) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ (FINITE' s) (FINITE' ((@INSERT A) x s)))))))) (∀ (λ a : El (fun A bool), (⇒ ((@FINITE A) a) (FINITE' a))))))) (∀ (λ a : El (fun A bool), (= ((@FINITE A) a) (∨ (= a (@EMPTY A)) (∃ (λ x : El A, (∃ (λ s : El (fun A bool), (∧ (= a ((@INSERT A) x s)) ((@FINITE A) s))))))))))));
