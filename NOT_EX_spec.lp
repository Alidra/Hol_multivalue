require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1123467 [_26368] : Prf (∀ (λ P : El (fun _26368 bool), (∀ (λ l : El (list _26368), (= (¬ ((@EX _26368) P l)) ((@ALL _26368) (λ x : El _26368, (¬ (P x))) l))))));
