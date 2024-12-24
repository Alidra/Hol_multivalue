require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6929990 [_126606] : Prf (∀ (λ f : El (fun _126606 num), (∀ (λ s : El (fun _126606 bool), (∀ (λ t : El (fun _126606 bool), (⇒ (∧ ((@FINITE _126606) s) ((@SUBSET _126606) t s)) (= ((@nsum _126606) ((@DIFF _126606) s t) f) (- ((@nsum _126606) s f) ((@nsum _126606) t f))))))))));
