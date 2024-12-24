require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7178808 [_135252] : Prf (∀ (λ f : El (fun _135252 real), (∀ (λ s : El (fun _135252 bool), (∀ (λ t : El (fun _135252 bool), (⇒ (∧ ((@FINITE _135252) s) (∧ ((@FINITE _135252) t) (∀ (λ x : El _135252, (⇒ ((@IN _135252) x ((@INTER _135252) s t)) (= (f x) (real_of_num (NUMERAL _0)))))))) (= ((@sum _135252) ((@UNION _135252) s t) f) (real_add ((@sum _135252) s f) ((@sum _135252) t f))))))))));
