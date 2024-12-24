require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3320763 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ x : El A, (= ((@INTER A) ((@DELETE A) s x) t) ((@DELETE A) ((@INTER A) s t) x))))))));
