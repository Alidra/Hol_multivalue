require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3460802 [_89711 _89725] (P : El (fun _89725 bool)) (f : El (fun _89725 (fun _89711 bool))) : Prf (∀ (λ x : El _89711, (= (∀ (λ t : El (fun _89711 bool), (⇒ (∃ (λ x' : El _89725, (∧ (P x') (= t (f x'))))) ((@IN _89711) x t)))) (∀ (λ x' : El _89725, (⇒ (P x') ((@IN _89711) x (f x'))))))));
