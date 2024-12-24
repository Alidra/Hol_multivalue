require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3462445 [_89769 _89788 _89789] (P : El (fun _89789 (fun _89788 bool))) (f : El (fun _89789 (fun _89788 (fun _89769 bool)))) : Prf (∀ (λ x : El _89769, (= (∀ (λ t : El (fun _89769 bool), (⇒ (∃ (λ x' : El _89789, (∃ (λ y : El _89788, (∧ (P x' y) (= t (f x' y))))))) ((@IN _89769) x t)))) (∀ (λ x' : El _89789, (∀ (λ y : El _89788, (⇒ (P x' y) ((@IN _89769) x (f x' y))))))))));
