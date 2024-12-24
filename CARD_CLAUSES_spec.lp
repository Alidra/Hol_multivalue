require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3840691 [A] : Prf (∧ (= ((@CARD A) (@EMPTY A)) (NUMERAL _0)) (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@CARD A) ((@INSERT A) x s)) ((@COND num) ((@IN A) x s) ((@CARD A) s) (SUC ((@CARD A) s))))))))));
