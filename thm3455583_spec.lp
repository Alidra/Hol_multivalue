require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3455583 [_89520 _89534] (P : El (fun _89534 bool)) (f : El (fun _89534 (fun _89520 bool))) : Prf (∀ (λ x : El _89520, (= (∃ (λ t : El (fun _89520 bool), (∧ (∃ (λ x' : El _89534, (∧ (P x') (= t (f x'))))) ((@IN _89520) x t)))) (∃ (λ x' : El _89534, (∧ (P x') ((@IN _89520) x (f x'))))))));
