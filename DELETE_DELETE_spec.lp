require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3307760 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (= ((@DELETE A) ((@DELETE A) s x) x) ((@DELETE A) s x))))));
