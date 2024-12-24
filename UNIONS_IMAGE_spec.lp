require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3452302 [_89422 _89438] : Prf (∀ (λ f : El (fun _89438 (fun _89422 bool)), (∀ (λ s : El (fun _89438 bool), (= ((@UNIONS _89422) ((@IMAGE _89438 (fun _89422 bool)) f s)) ((@GSPEC _89422) (λ GEN_PVAR_47 : El _89422, (∃ (λ y : El _89422, ((@SETSPEC _89422) GEN_PVAR_47 (∃ (λ x : El _89438, (∧ ((@IN _89438) x s) ((@IN _89422) y (f x))))) y))))))))));
