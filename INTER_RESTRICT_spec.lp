require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3261090 [_85450] : Prf (∀ (λ P : El (fun _85450 bool), (∀ (λ s : El (fun _85450 bool), (∀ (λ t : El (fun _85450 bool), (= ((@GSPEC _85450) (λ GEN_PVAR_15 : El _85450, (∃ (λ x : El _85450, ((@SETSPEC _85450) GEN_PVAR_15 (∧ ((@IN _85450) x ((@INTER _85450) s t)) (P x)) x))))) ((@INTER _85450) ((@GSPEC _85450) (λ GEN_PVAR_16 : El _85450, (∃ (λ x : El _85450, ((@SETSPEC _85450) GEN_PVAR_16 (∧ ((@IN _85450) x s) (P x)) x))))) ((@GSPEC _85450) (λ GEN_PVAR_17 : El _85450, (∃ (λ x : El _85450, ((@SETSPEC _85450) GEN_PVAR_17 (∧ ((@IN _85450) x t) (P x)) x)))))))))))));
