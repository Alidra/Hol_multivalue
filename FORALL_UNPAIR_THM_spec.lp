require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem53965 [_5486 _5488] : Prf (∀ (λ P : El (fun _5486 (fun _5488 bool)), (= (∀ (λ x : El _5486, (∀ (λ y : El _5488, (P x y))))) (∀ (λ z : El (prod _5486 _5488), (P ((@FST _5486 _5488) z) ((@SND _5486 _5488) z)))))));
