require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1206100 [_28223] (l : El (list _28223)) : Prf (∀ (λ n : El num, (= ((@EL _28223) n ((@TL _28223) l)) ((@EL _28223) (+ n (NUMERAL (BIT1 _0))) l))));
