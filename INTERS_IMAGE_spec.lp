require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3453847 [_89465 _89481] : Prf (∀ (λ f : El (fun _89481 (fun _89465 bool)), (∀ (λ s : El (fun _89481 bool), (= ((@INTERS _89465) ((@IMAGE _89481 (fun _89465 bool)) f s)) ((@GSPEC _89465) (λ GEN_PVAR_48 : El _89465, (∃ (λ y : El _89465, ((@SETSPEC _89465) GEN_PVAR_48 (∀ (λ x : El _89481, (⇒ ((@IN _89481) x s) ((@IN _89465) y (f x))))) y))))))))));
