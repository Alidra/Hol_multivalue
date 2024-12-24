require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1094347 [A] (P : El (fun (list A) bool)) : Prf (= ((λ P' : El (fun (list A) bool), (⇒ (∧ (P' (@NIL A)) (∀ (λ h : El A, (∀ (λ t : El (list A), (⇒ (P' t) (P' ((@CONS A) h t)))))))) (∀ (λ l : El (list A), (P' l))))) P) (⇒ (∧ (P (@NIL A)) (∀ (λ h : El A, (∀ (λ t : El (list A), (⇒ (P t) (P ((@CONS A) h t)))))))) (∀ (λ l : El (list A), (P l)))));
