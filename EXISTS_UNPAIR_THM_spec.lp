require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem54104 [_5515 _5517] : Prf (∀ (λ P : El (fun _5515 (fun _5517 bool)), (= (∃ (λ x : El _5515, (∃ (λ y : El _5517, (P x y))))) (∃ (λ z : El (prod _5515 _5517), (P ((@FST _5515 _5517) z) ((@SND _5515 _5517) z)))))));
