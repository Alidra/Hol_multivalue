require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6903343 [_126132 _126171] : Prf (∧ (∀ (λ f : El (fun _126132 num), (= ((@nproduct _126132) (@EMPTY _126132) f) (NUMERAL (BIT1 _0))))) (∀ (λ x : El _126171, (∀ (λ f : El (fun _126171 num), (∀ (λ s : El (fun _126171 bool), (⇒ ((@FINITE _126171) s) (= ((@nproduct _126171) ((@INSERT _126171) x s) f) ((@COND num) ((@IN _126171) x s) ((@nproduct _126171) s f) (* (f x) ((@nproduct _126171) s f))))))))))));
