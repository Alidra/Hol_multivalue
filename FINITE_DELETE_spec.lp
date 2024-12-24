require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3610594 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (= ((@FINITE A) ((@DELETE A) s x)) ((@FINITE A) s))))));
