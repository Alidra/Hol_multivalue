require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1124075 [_26443] (R : El (fun _26443 bool)) (P : El (fun _26443 bool)) (Q : El (fun _26443 bool)) : Prf (∀ (λ l : El (list _26443), (⇒ (∧ ((@ALL _26443) R l) (∀ (λ x : El _26443, (⇒ (R x) (= (P x) (Q x)))))) (= ((@ALL _26443) P l) ((@ALL _26443) Q l)))));
