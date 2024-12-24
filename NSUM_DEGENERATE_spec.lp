require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6924730 [_126453] : Prf (∀ (λ f : El (fun _126453 num), (∀ (λ s : El (fun _126453 bool), (⇒ (¬ ((@FINITE _126453) ((@GSPEC _126453) (λ GEN_PVAR_284 : El _126453, (∃ (λ x : El _126453, ((@SETSPEC _126453) GEN_PVAR_284 (∧ ((@IN _126453) x s) (¬ (= (f x) (NUMERAL _0)))) x))))))) (= ((@nsum _126453) s f) (NUMERAL _0)))))));
