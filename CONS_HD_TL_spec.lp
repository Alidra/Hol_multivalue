require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1207006 [_28337] : Prf (∀ (λ l : El (list _28337), (⇒ (¬ (= l (@NIL _28337))) (= l ((@CONS _28337) ((@HD _28337) l) ((@TL _28337) l))))));
