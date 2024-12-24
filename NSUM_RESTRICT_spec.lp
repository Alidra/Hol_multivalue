require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6970340 [_127848] : Prf (∀ (λ f : El (fun _127848 num), (∀ (λ s : El (fun _127848 bool), (⇒ ((@FINITE _127848) s) (= ((@nsum _127848) s (λ x : El _127848, ((@COND num) ((@IN _127848) x s) (f x) (NUMERAL _0)))) ((@nsum _127848) s f)))))));
