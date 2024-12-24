require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6925097 [_126551] : Prf (∀ (λ f : El (fun _126551 num), (∀ (λ s : El (fun _126551 bool), (∀ (λ t : El (fun _126551 bool), (⇒ (∧ ((@FINITE _126551) s) (∧ ((@FINITE _126551) t) ((@DISJOINT _126551) s t))) (= ((@nsum _126551) ((@UNION _126551) s t) f) (+ ((@nsum _126551) s f) ((@nsum _126551) t f))))))))));
