require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1133441 [_26720] (P : El (fun _26720 bool)) (Q : El (fun _26720 bool)) : Prf (∀ (λ l : El (list _26720), (= (∧ ((@ALL _26720) P l) ((@ALL _26720) Q l)) ((@ALL _26720) (λ x : El _26720, (∧ (P x) (Q x))) l))));
