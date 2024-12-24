require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4354438 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ s' : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ t' : El (fun B bool), (= (= ((@CROSS B A) s t) ((@CROSS B A) s' t')) (∨ (∧ (∨ (= s (@EMPTY A)) (= t (@EMPTY B))) (∨ (= s' (@EMPTY A)) (= t' (@EMPTY B)))) (∧ (= s s') (= t t'))))))))))));
