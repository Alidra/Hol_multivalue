require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1123621 [_26390] : Prf (∀ (λ P : El (fun _26390 bool), (∀ (λ l : El (list _26390), (= (¬ ((@ALL _26390) P l)) ((@EX _26390) (λ x : El _26390, (¬ (P x))) l))))));
