require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1162240 [_27312] : Prf (∀ (λ l : El (list _27312), (∀ (λ x : El _27312, (= ((@MEM _27312) x l) (∃ (λ i : El num, (∧ (< i ((@LENGTH _27312) l)) (= x ((@EL _27312) i l))))))))));
