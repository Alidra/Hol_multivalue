require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1101585 [_25328] : Prf (∀ (λ h : El _25328, (∀ (λ P : El (fun _25328 bool), (∀ (λ t : El (list _25328), (= ((@EX _25328) P ((@CONS _25328) h t)) (∨ (P h) ((@EX _25328) P t)))))))));
