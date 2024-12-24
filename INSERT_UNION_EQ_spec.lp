require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3282369 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@UNION A) ((@INSERT A) x s) t) ((@INSERT A) x ((@UNION A) s t)))))))));
