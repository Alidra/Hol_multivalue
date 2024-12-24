require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1206724 [_28274] : Prf (∀ (λ l : El (list _28274), (⇒ (¬ (= l (@NIL _28274))) (= ((@LAST _28274) l) ((@EL _28274) (- ((@LENGTH _28274) l) (NUMERAL (BIT1 _0))) l)))));
