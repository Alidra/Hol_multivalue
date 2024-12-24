require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6924916 [_126486 _126525] : Prf (∧ (∀ (λ f : El (fun _126486 num), (= ((@nsum _126486) (@EMPTY _126486) f) (NUMERAL _0)))) (∀ (λ x : El _126525, (∀ (λ f : El (fun _126525 num), (∀ (λ s : El (fun _126525 bool), (⇒ ((@FINITE _126525) s) (= ((@nsum _126525) ((@INSERT _126525) x s) f) ((@COND num) ((@IN _126525) x s) ((@nsum _126525) s f) (+ (f x) ((@nsum _126525) s f))))))))))));
