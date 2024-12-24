require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3239807 [_84925] : Prf (∀ (λ P : El (fun _84925 bool), (∀ (λ s : El (fun _84925 bool), (∀ (λ t : El (fun _84925 bool), (= ((@GSPEC _84925) (λ GEN_PVAR_12 : El _84925, (∃ (λ x : El _84925, ((@SETSPEC _84925) GEN_PVAR_12 (∧ ((@IN _84925) x ((@UNION _84925) s t)) (P x)) x))))) ((@UNION _84925) ((@GSPEC _84925) (λ GEN_PVAR_13 : El _84925, (∃ (λ x : El _84925, ((@SETSPEC _84925) GEN_PVAR_13 (∧ ((@IN _84925) x s) (P x)) x))))) ((@GSPEC _84925) (λ GEN_PVAR_14 : El _84925, (∃ (λ x : El _84925, ((@SETSPEC _84925) GEN_PVAR_14 (∧ ((@IN _84925) x t) (P x)) x)))))))))))));
