require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4668 [_910] : Prf (∀ (λ P : El (fun _910 bool), (∀ (λ a : El _910, (= (∀ (λ x : El _910, (⇒ (= a x) (P x)))) (P a))))));
