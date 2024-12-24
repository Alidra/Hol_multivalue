require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6930107 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ f : El (fun A num), (⇒ (∧ ((@FINITE A) s) ((@FINITE A) t)) (= (+ ((@nsum A) s f) ((@nsum A) t f)) (+ ((@nsum A) ((@UNION A) s t) f) ((@nsum A) ((@INTER A) s t) f))))))))));
