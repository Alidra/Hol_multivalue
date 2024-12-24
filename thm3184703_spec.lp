require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3184703 [_83169] (p : El (fun _83169 bool)) : Prf (∀ (λ x : El _83169, (= ((@IN _83169) x (λ y : El _83169, (p y))) (p x))));
