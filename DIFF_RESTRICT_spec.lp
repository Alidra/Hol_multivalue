require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3271962 [_85837] : Prf (∀ (λ P : El (fun _85837 bool), (∀ (λ s : El (fun _85837 bool), (∀ (λ t : El (fun _85837 bool), (= ((@GSPEC _85837) (λ GEN_PVAR_18 : El _85837, (∃ (λ x : El _85837, ((@SETSPEC _85837) GEN_PVAR_18 (∧ ((@IN _85837) x ((@DIFF _85837) s t)) (P x)) x))))) ((@DIFF _85837) ((@GSPEC _85837) (λ GEN_PVAR_19 : El _85837, (∃ (λ x : El _85837, ((@SETSPEC _85837) GEN_PVAR_19 (∧ ((@IN _85837) x s) (P x)) x))))) ((@GSPEC _85837) (λ GEN_PVAR_20 : El _85837, (∃ (λ x : El _85837, ((@SETSPEC _85837) GEN_PVAR_20 (∧ ((@IN _85837) x t) (P x)) x)))))))))))));
