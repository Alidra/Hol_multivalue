require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3258370 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (= ((@INTER A) (@EMPTY A) s) (@EMPTY A)))) (∀ (λ s : El (fun A bool), (= ((@INTER A) s (@EMPTY A)) (@EMPTY A)))));
