require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3237011 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= (= ((@UNION A) s t) (@EMPTY A)) (∧ (= s (@EMPTY A)) (= t (@EMPTY A))))))));
