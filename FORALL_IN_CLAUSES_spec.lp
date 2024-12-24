require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5031264 [_113480 _113520] : Prf (∧ (∀ (λ P : El (fun _113480 bool), (= (∀ (λ x : El _113480, (⇒ ((@IN _113480) x (@EMPTY _113480)) (P x)))) T))) (∀ (λ P : El (fun _113520 bool), (∀ (λ a : El _113520, (∀ (λ s : El (fun _113520 bool), (= (∀ (λ x : El _113520, (⇒ ((@IN _113520) x ((@INSERT _113520) a s)) (P x)))) (∧ (P a) (∀ (λ x : El _113520, (⇒ ((@IN _113520) x s) (P x)))))))))))));
