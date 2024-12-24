require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6930693 [_126816] : Prf (∀ (λ f : El (fun _126816 num), (∀ (λ g : El (fun _126816 num), (∀ (λ s : El (fun _126816 bool), (⇒ (∧ ((@FINITE _126816) ((@GSPEC _126816) (λ GEN_PVAR_285 : El _126816, (∃ (λ x : El _126816, ((@SETSPEC _126816) GEN_PVAR_285 (∧ ((@IN _126816) x s) (¬ (= (f x) (NUMERAL _0)))) x)))))) ((@FINITE _126816) ((@GSPEC _126816) (λ GEN_PVAR_286 : El _126816, (∃ (λ x : El _126816, ((@SETSPEC _126816) GEN_PVAR_286 (∧ ((@IN _126816) x s) (¬ (= (g x) (NUMERAL _0)))) x))))))) (= ((@nsum _126816) s (λ x : El _126816, (+ (f x) (g x)))) (+ ((@nsum _126816) s f) ((@nsum _126816) s g))))))))));
