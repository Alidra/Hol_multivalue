require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3207453 [_83983] : Prf (∀ (λ P : El (fun _83983 bool), (∀ (λ a : El _83983, (∀ (λ s : El (fun _83983 bool), (= (∀ (λ x : El _83983, (⇒ ((@IN _83983) x ((@INSERT _83983) a s)) (P x)))) (∧ (P a) (∀ (λ x : El _83983, (⇒ ((@IN _83983) x s) (P x))))))))))));
