require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3947439 [_101385] : Prf (∀ (λ s : El (fun _101385 bool), (∀ (λ t : El (fun _101385 bool), (⇒ (∧ ((@FINITE _101385) s) ((@FINITE _101385) t)) (= ((@CARD _101385) ((@UNION _101385) s t)) (- (+ ((@CARD _101385) s) ((@CARD _101385) t)) ((@CARD _101385) ((@INTER _101385) s t)))))))));
