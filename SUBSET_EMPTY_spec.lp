require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3220121 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@SUBSET A) s (@EMPTY A)) (= s (@EMPTY A)))));
