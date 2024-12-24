require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3843862 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE A) t) (= ((@INTER A) s t) (@EMPTY A)))) (= ((@CARD A) ((@UNION A) s t)) (+ ((@CARD A) s) ((@CARD A) t))))))));
