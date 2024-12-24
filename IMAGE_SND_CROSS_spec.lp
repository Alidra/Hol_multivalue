require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4357468 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (= ((@IMAGE (prod A B) B) (@SND A B) ((@CROSS B A) s t)) ((@COND (fun B bool)) (= s (@EMPTY A)) (@EMPTY B) t))))));
