require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3322076 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ x : El A, (= ((@DISJOINT A) ((@DELETE A) s x) t) ((@DISJOINT A) ((@DELETE A) t x) s))))))));
