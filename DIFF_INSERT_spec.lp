require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3313024 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ x : El A, (= ((@DIFF A) s ((@INSERT A) x t)) ((@DIFF A) ((@DELETE A) s x) t))))))));
