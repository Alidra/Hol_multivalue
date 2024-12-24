require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1203021 [_28101] : Prf (∀ (λ p : El (list _28101), (∀ (λ q : El (list _28101), (= ((@LAST _28101) ((@APPEND _28101) p q)) ((@COND _28101) (= q (@NIL _28101)) ((@LAST _28101) p) ((@LAST _28101) q)))))));
