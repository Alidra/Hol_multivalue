require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3854223 [_99873] : Prf (∀ (λ s : El (fun _99873 bool), (∀ (λ t : El (fun _99873 bool), (⇒ (∧ ((@FINITE _99873) s) ((@SUBSET _99873) t s)) (= ((@CARD _99873) ((@DIFF _99873) s t)) (- ((@CARD _99873) s) ((@CARD _99873) t))))))));
