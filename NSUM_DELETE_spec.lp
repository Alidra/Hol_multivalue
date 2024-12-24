require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6960522 [_127419] : Prf (∀ (λ f : El (fun _127419 num), (∀ (λ s : El (fun _127419 bool), (∀ (λ a : El _127419, (⇒ (∧ ((@FINITE _127419) s) ((@IN _127419) a s)) (= (+ (f a) ((@nsum _127419) ((@DELETE _127419) s a) f)) ((@nsum _127419) s f)))))))));
