require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6930477 [_126729] : Prf (∀ (λ f : El (fun _126729 num), (∀ (λ g : El (fun _126729 num), (∀ (λ s : El (fun _126729 bool), (⇒ ((@FINITE _126729) s) (= ((@nsum _126729) s (λ x : El _126729, (+ (f x) (g x)))) (+ ((@nsum _126729) s f) ((@nsum _126729) s g))))))))));
