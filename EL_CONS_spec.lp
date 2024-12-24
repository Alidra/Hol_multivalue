require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1206267 [_28249] : Prf (∀ (λ n : El num, (∀ (λ h : El _28249, (∀ (λ t : El (list _28249), (= ((@EL _28249) n ((@CONS _28249) h t)) ((@COND _28249) (= n (NUMERAL _0)) h ((@EL _28249) (- n (NUMERAL (BIT1 _0))) t)))))))));
