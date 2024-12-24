require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1098917 [_25251] : Prf (∧ (= ((@BUTLAST _25251) (@NIL _25251)) (@NIL _25251)) (∀ (λ h : El _25251, (∀ (λ t : El (list _25251), (= ((@BUTLAST _25251) ((@CONS _25251) h t)) ((@COND (list _25251)) (= t (@NIL _25251)) (@NIL _25251) ((@CONS _25251) h ((@BUTLAST _25251) t)))))))));
