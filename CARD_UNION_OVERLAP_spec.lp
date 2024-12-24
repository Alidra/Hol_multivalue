require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3971264 [_101508] : Prf (∀ (λ s : El (fun _101508 bool), (∀ (λ t : El (fun _101508 bool), (⇒ (∧ ((@FINITE _101508) s) (∧ ((@FINITE _101508) t) (< ((@CARD _101508) ((@UNION _101508) s t)) (+ ((@CARD _101508) s) ((@CARD _101508) t))))) (¬ (= ((@INTER _101508) s t) (@EMPTY _101508))))))));
