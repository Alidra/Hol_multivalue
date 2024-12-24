require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1118281 [_26221] : Prf (∀ (λ l : El (list _26221), (∀ (λ n : El num, (= (= ((@LENGTH _26221) l) (SUC n)) (∃ (λ h : El _26221, (∃ (λ t : El (list _26221), (∧ (= l ((@CONS _26221) h t)) (= ((@LENGTH _26221) t) n)))))))))));
