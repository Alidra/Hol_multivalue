require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1123794 [_26411 _26412] : Prf (∀ (λ P : El (fun _26412 bool), (∀ (λ f : El (fun _26411 _26412), (∀ (λ l : El (list _26411), (= ((@ALL _26412) P ((@MAP _26411 _26412) f l)) ((@ALL _26411) ((@o _26411 _26412 bool) P f) l))))))));
