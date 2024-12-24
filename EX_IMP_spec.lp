require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1135797 [_26750] : Prf (∀ (λ P : El (fun _26750 bool), (∀ (λ Q : El (fun _26750 bool), (∀ (λ l : El (list _26750), (⇒ (∧ (∀ (λ x : El _26750, (⇒ (∧ ((@MEM _26750) x l) (P x)) (Q x)))) ((@EX _26750) P l)) ((@EX _26750) Q l))))))));
