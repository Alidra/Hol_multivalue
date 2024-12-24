require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4108815 [A] : Prf (∀ (λ f : El (fun (fun A bool) bool), (∀ (λ n : El num, (⇒ (∧ (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∧ ((@IN (fun A bool)) t f) ((@IN (fun A bool)) u f)) (∨ ((@SUBSET A) t u) ((@SUBSET A) u t))))))) (∀ (λ t : El (fun A bool), (⇒ ((@IN (fun A bool)) t f) (∧ ((@FINITE A) t) (<= ((@CARD A) t) n)))))) (∧ ((@FINITE A) ((@UNIONS A) f)) (<= ((@CARD A) ((@UNIONS A) f)) n)))))));
