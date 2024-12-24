require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1133060 [_26690] : Prf (∀ (λ P : El (fun _26690 bool), (∀ (λ Q : El (fun _26690 bool), (∀ (λ l : El (list _26690), (⇒ (∧ ((@ALL _26690) (λ x : El _26690, (⇒ (P x) (Q x))) l) ((@ALL _26690) P l)) ((@ALL _26690) Q l))))))));
