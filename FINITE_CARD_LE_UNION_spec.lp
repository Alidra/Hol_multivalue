require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3926921 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (∧ ((@FINITE A) s) (<= ((@CARD A) s) m)) (∧ ((@FINITE A) t) (<= ((@CARD A) t) n))) (∧ ((@FINITE A) ((@UNION A) s t)) (<= ((@CARD A) ((@UNION A) s t)) (+ m n))))))))))));
