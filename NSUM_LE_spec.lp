require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6933015 [_127006] : Prf (∀ (λ f : El (fun _127006 num), (∀ (λ g : El (fun _127006 num), (∀ (λ s : El (fun _127006 bool), (⇒ (∧ ((@FINITE _127006) s) (∀ (λ x : El _127006, (⇒ ((@IN _127006) x s) (<= (f x) (g x)))))) (<= ((@nsum _127006) s f) ((@nsum _127006) s g)))))))));
