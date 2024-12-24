require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3235853 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (= ((@UNION A) (@EMPTY A) s) s))) (∀ (λ s : El (fun A bool), (= ((@UNION A) s (@EMPTY A)) s))));
