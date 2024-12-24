require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1123316 [_26340] : Prf (∀ (λ P : El (fun _26340 bool), (∀ (λ Q : El (fun _26340 bool), (∀ (λ l : El (list _26340), (⇒ (∧ (∀ (λ x : El _26340, (⇒ (∧ ((@MEM _26340) x l) (P x)) (Q x)))) ((@ALL _26340) P l)) ((@ALL _26340) Q l))))))));
