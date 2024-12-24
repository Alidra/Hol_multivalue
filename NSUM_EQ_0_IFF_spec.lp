require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6954254 [_127305] (f : El (fun _127305 num)) : Prf (∀ (λ s : El (fun _127305 bool), (⇒ ((@FINITE _127305) s) (= (= ((@nsum _127305) s f) (NUMERAL _0)) (∀ (λ x : El _127305, (⇒ ((@IN _127305) x s) (= (f x) (NUMERAL _0)))))))));
