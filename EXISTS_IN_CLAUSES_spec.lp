require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5032597 [_113540 _113580] : Prf (∧ (∀ (λ P : El (fun _113540 bool), (= (∃ (λ x : El _113540, (∧ ((@IN _113540) x (@EMPTY _113540)) (P x)))) F))) (∀ (λ P : El (fun _113580 bool), (∀ (λ a : El _113580, (∀ (λ s : El (fun _113580 bool), (= (∃ (λ x : El _113580, (∧ ((@IN _113580) x ((@INSERT _113580) a s)) (P x)))) (∨ (P a) (∃ (λ x : El _113580, (∧ ((@IN _113580) x s) (P x)))))))))))));
