require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4355951 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (= ((@IMAGE (prod A B) A) (@FST A B) ((@CROSS B A) s t)) ((@COND (fun A bool)) (= t (@EMPTY B)) (@EMPTY A) s))))));
