require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1152665 [_27073] : Prf (∀ (λ P : El (fun _27073 bool), (∀ (λ l : El (list _27073), (∀ (λ x : El _27073, (= ((@MEM _27073) x ((@FILTER _27073) P l)) (∧ (P x) ((@MEM _27073) x l)))))))));
