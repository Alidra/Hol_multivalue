require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1145802 [_26945] : Prf (∀ (λ x : El _26945, (∀ (λ l1 : El (list _26945), (∀ (λ l2 : El (list _26945), (= ((@MEM _26945) x ((@APPEND _26945) l1 l2)) (∨ ((@MEM _26945) x l1) ((@MEM _26945) x l2)))))))));
