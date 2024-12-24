require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3458943 [_89578 _89597 _89598] (P : El (fun _89598 (fun _89597 bool))) (f : El (fun _89598 (fun _89597 (fun _89578 bool)))) : Prf (= ((@UNIONS _89578) ((@GSPEC (fun _89578 bool)) (λ GEN_PVAR_51 : El (fun _89578 bool), (∃ (λ x : El _89598, (∃ (λ y : El _89597, ((@SETSPEC (fun _89578 bool)) GEN_PVAR_51 (P x y) (f x y))))))))) ((@GSPEC _89578) (λ GEN_PVAR_52 : El _89578, (∃ (λ a : El _89578, ((@SETSPEC _89578) GEN_PVAR_52 (∃ (λ x : El _89598, (∃ (λ y : El _89597, (∧ (P x y) ((@IN _89578) a (f x y))))))) a))))));
