require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7018613 [_129614] : Prf (∀ (λ f : El (fun _129614 num), (∀ (λ s : El (fun _129614 bool), (∀ (λ t : El (fun _129614 bool), (⇒ (∧ ((@FINITE _129614) s) (∧ ((@FINITE _129614) t) (∀ (λ x : El _129614, (⇒ ((@IN _129614) x ((@INTER _129614) s t)) (= (f x) (NUMERAL _0))))))) (= ((@nsum _129614) ((@UNION _129614) s t) f) (+ ((@nsum _129614) s f) ((@nsum _129614) t f))))))))));
