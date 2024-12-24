require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4380688 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ s' : El (fun A bool), (∀ (λ t' : El (fun B bool), (= ((@DISJOINT (prod A B)) ((@CROSS B A) s t) ((@CROSS B A) s' t')) (∨ ((@DISJOINT A) s s') ((@DISJOINT B) t t')))))))))));
