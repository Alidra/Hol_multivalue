require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6986989 [_128167] (f : El (fun _128167 num)) : Prf (∀ (λ s : El (fun _128167 bool), (∀ (λ t : El (fun _128167 bool), (∀ (λ u : El (fun _128167 bool), (⇒ (∧ ((@FINITE _128167) u) (∧ (= ((@INTER _128167) s t) (@EMPTY _128167)) (= ((@UNION _128167) s t) u))) (= (+ ((@nsum _128167) s f) ((@nsum _128167) t f)) ((@nsum _128167) u f)))))))));
