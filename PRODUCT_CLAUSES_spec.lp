require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6912941 [_126288 _126329] : Prf (∧ (∀ (λ f : El (fun _126288 real), (= ((@product _126288) (@EMPTY _126288) f) (real_of_num (NUMERAL (BIT1 _0)))))) (∀ (λ x : El _126329, (∀ (λ f : El (fun _126329 real), (∀ (λ s : El (fun _126329 bool), (⇒ ((@FINITE _126329) s) (= ((@product _126329) ((@INSERT _126329) x s) f) ((@COND real) ((@IN _126329) x s) ((@product _126329) s f) (real_mul (f x) ((@product _126329) s f))))))))))));
