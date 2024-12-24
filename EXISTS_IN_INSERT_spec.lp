require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3208694 [_84024] : Prf (∀ (λ P : El (fun _84024 bool), (∀ (λ a : El _84024, (∀ (λ s : El (fun _84024 bool), (= (∃ (λ x : El _84024, (∧ ((@IN _84024) x ((@INSERT _84024) a s)) (P x)))) (∨ (P a) (∃ (λ x : El _84024, (∧ ((@IN _84024) x s) (P x))))))))))));
