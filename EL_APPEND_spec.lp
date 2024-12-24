require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1206051 [_28192] : Prf (∀ (λ k : El num, (∀ (λ l : El (list _28192), (∀ (λ m : El (list _28192), (= ((@EL _28192) k ((@APPEND _28192) l m)) ((@COND _28192) (< k ((@LENGTH _28192) l)) ((@EL _28192) k l) ((@EL _28192) (- k ((@LENGTH _28192) l)) m)))))))));
