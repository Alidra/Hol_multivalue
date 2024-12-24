require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3258568 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (= ((@INTER A) (@UNIV A) s) s))) (∀ (λ s : El (fun A bool), (= ((@INTER A) s (@UNIV A)) s))));
