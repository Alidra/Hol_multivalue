require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem297 [_216] (P : El (fun _216 bool)) (Q : El bool) : Prf (= (∀ (λ x : El _216, (⇒ (P x) Q))) (⇒ (∃ (λ x : El _216, (P x))) Q));
