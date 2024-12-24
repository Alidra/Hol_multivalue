require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3845383 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@CARD A) ((@DELETE A) s x)) ((@COND num) ((@IN A) x s) (- ((@CARD A) s) (NUMERAL (BIT1 _0))) ((@CARD A) s))))))));
