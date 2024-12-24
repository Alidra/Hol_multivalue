require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3311905 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@SUBSET A) s ((@INSERT A) x t)) ((@SUBSET A) ((@DELETE A) s x) t))))))));
