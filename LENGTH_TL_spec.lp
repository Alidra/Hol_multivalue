require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1203798 [_28117] : Prf (∀ (λ l : El (list _28117), (⇒ (¬ (= l (@NIL _28117))) (= ((@LENGTH _28117) ((@TL _28117) l)) (- ((@LENGTH _28117) l) (NUMERAL (BIT1 _0)))))));
