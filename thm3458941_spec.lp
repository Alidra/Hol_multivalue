require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3458941 [_89520 _89534] (P : El (fun _89534 bool)) (f : El (fun _89534 (fun _89520 bool))) : Prf (∀ (λ x : El _89520, (= ((@IN _89520) x ((@UNIONS _89520) ((@GSPEC (fun _89520 bool)) (λ GEN_PVAR_49 : El (fun _89520 bool), (∃ (λ x' : El _89534, ((@SETSPEC (fun _89520 bool)) GEN_PVAR_49 (P x') (f x')))))))) ((@IN _89520) x ((@GSPEC _89520) (λ GEN_PVAR_50 : El _89520, (∃ (λ a : El _89520, ((@SETSPEC _89520) GEN_PVAR_50 (∃ (λ x' : El _89534, (∧ (P x') ((@IN _89520) a (f x'))))) a)))))))));
