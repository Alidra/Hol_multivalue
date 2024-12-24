require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1110669 [A] : Prf (∧ (∀ (λ r : El (fun A (fun A bool)), (= ((@PAIRWISE A) r (@NIL A)) T))) (∀ (λ h : El A, (∀ (λ r : El (fun A (fun A bool)), (∀ (λ t : El (list A), (= ((@PAIRWISE A) r ((@CONS A) h t)) (∧ ((@ALL A) (r h) t) ((@PAIRWISE A) r t))))))))));
