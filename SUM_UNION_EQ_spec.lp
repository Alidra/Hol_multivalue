require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7153073 [_133751] (f : El (fun _133751 real)) : Prf (∀ (λ s : El (fun _133751 bool), (∀ (λ t : El (fun _133751 bool), (∀ (λ u : El (fun _133751 bool), (⇒ (∧ ((@FINITE _133751) u) (∧ (= ((@INTER _133751) s t) (@EMPTY _133751)) (= ((@UNION _133751) s t) u))) (= (real_add ((@sum _133751) s f) ((@sum _133751) t f)) ((@sum _133751) u f)))))))));
