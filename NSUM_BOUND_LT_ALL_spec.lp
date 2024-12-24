require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6980150 [_128066] : Prf (∀ (λ s : El (fun _128066 bool), (∀ (λ f : El (fun _128066 num), (∀ (λ b : El num, (⇒ (∧ ((@FINITE _128066) s) (∧ (¬ (= s (@EMPTY _128066))) (∀ (λ x : El _128066, (⇒ ((@IN _128066) x s) (< (f x) b)))))) (< ((@nsum _128066) s f) (* ((@CARD _128066) s) b)))))))));
