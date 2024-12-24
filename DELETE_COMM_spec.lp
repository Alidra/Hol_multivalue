require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3308927 [A] : Prf (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El (fun A bool), (= ((@DELETE A) ((@DELETE A) s x) y) ((@DELETE A) ((@DELETE A) s y) x))))))));
