require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1138070 [_26777] : Prf (∀ (λ P : El (fun _26777 bool), (∀ (λ l : El (list _26777), (= (∀ (λ x : El _26777, (⇒ ((@MEM _26777) x l) (P x)))) ((@ALL _26777) P l))))));
