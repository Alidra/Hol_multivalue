require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6919131 [_126367 _126408] : Prf (∧ (∀ (λ f : El (fun _126367 int), (= ((@isum _126367) (@EMPTY _126367) f) (int_of_num (NUMERAL _0))))) (∀ (λ x : El _126408, (∀ (λ f : El (fun _126408 int), (∀ (λ s : El (fun _126408 bool), (⇒ ((@FINITE _126408) s) (= ((@isum _126408) ((@INSERT _126408) x s) f) ((@COND int) ((@IN _126408) x s) ((@isum _126408) s f) (int_add (f x) ((@isum _126408) s f))))))))))));
