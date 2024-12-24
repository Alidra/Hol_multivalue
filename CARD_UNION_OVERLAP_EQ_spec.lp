require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3969598 [_101466] : Prf (∀ (λ s : El (fun _101466 bool), (∀ (λ t : El (fun _101466 bool), (⇒ (∧ ((@FINITE _101466) s) ((@FINITE _101466) t)) (= (= ((@CARD _101466) ((@UNION _101466) s t)) (+ ((@CARD _101466) s) ((@CARD _101466) t))) (= ((@INTER _101466) s t) (@EMPTY _101466))))))));
