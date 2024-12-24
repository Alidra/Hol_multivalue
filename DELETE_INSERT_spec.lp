require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3318884 [A] : Prf (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El (fun A bool), (= ((@DELETE A) ((@INSERT A) x s) y) ((@COND (fun A bool)) (= x y) ((@DELETE A) s y) ((@INSERT A) x ((@DELETE A) s y))))))))));
