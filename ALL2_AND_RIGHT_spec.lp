require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1129352 [_26588 _26589] : Prf (∀ (λ l : El (list _26589), (∀ (λ m : El (list _26588), (∀ (λ P : El (fun _26589 bool), (∀ (λ Q : El (fun _26589 (fun _26588 bool)), (= ((@ALL2 _26589 _26588) (λ x : El _26589, (λ y : El _26588, (∧ (P x) (Q x y)))) l m) (∧ ((@ALL _26589) P l) ((@ALL2 _26589 _26588) Q l m)))))))))));
