require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1202159 [_28076] : Prf (∀ (λ l : El (list _28076), (⇒ (¬ (= l (@NIL _28076))) (= ((@APPEND _28076) ((@BUTLAST _28076) l) ((@CONS _28076) ((@LAST _28076) l) (@NIL _28076))) l))));
