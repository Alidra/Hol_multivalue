require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4624119 : Prf (∀ (λ s : El (fun num bool), (= ((@FINITE num) s) (∃ (λ a : El num, (∀ (λ x : El num, (⇒ ((@IN num) x s) (<= x a)))))))));
