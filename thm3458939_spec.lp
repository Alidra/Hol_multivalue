require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3458939 [_89646 _89670 _89671 _89672] (P : El (fun _89672 (fun _89671 (fun _89670 bool)))) (f : El (fun _89672 (fun _89671 (fun _89670 (fun _89646 bool))))) : Prf (∀ (λ x : El _89646, (= ((@IN _89646) x ((@UNIONS _89646) ((@GSPEC (fun _89646 bool)) (λ GEN_PVAR_53 : El (fun _89646 bool), (∃ (λ x' : El _89672, (∃ (λ y : El _89671, (∃ (λ z : El _89670, ((@SETSPEC (fun _89646 bool)) GEN_PVAR_53 (P x' y z) (f x' y z)))))))))))) ((@IN _89646) x ((@GSPEC _89646) (λ GEN_PVAR_54 : El _89646, (∃ (λ a : El _89646, ((@SETSPEC _89646) GEN_PVAR_54 (∃ (λ x' : El _89672, (∃ (λ y : El _89671, (∃ (λ z : El _89670, (∧ (P x' y z) ((@IN _89646) a (f x' y z))))))))) a)))))))));
