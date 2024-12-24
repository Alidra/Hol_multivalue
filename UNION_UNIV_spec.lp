require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3236047 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (= ((@UNION A) (@UNIV A) s) (@UNIV A)))) (∀ (λ s : El (fun A bool), (= ((@UNION A) s (@UNIV A)) (@UNIV A)))));
