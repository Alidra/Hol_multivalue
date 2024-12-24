require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3457131 [_89578 _89597 _89598] (P : El (fun _89598 (fun _89597 bool))) (f : El (fun _89598 (fun _89597 (fun _89578 bool)))) : Prf (∀ (λ x : El _89578, (= (∃ (λ t : El (fun _89578 bool), (∧ (∃ (λ x' : El _89598, (∃ (λ y : El _89597, (∧ (P x' y) (= t (f x' y))))))) ((@IN _89578) x t)))) (∃ (λ x' : El _89598, (∃ (λ y : El _89597, (∧ (P x' y) ((@IN _89578) x (f x' y))))))))));
