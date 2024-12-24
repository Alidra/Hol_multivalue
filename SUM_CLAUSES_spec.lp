require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7067645 [_131483 _131524] : Prf (∧ (∀ (λ f : El (fun _131483 real), (= ((@sum _131483) (@EMPTY _131483) f) (real_of_num (NUMERAL _0))))) (∀ (λ x : El _131524, (∀ (λ f : El (fun _131524 real), (∀ (λ s : El (fun _131524 bool), (⇒ ((@FINITE _131524) s) (= ((@sum _131524) ((@INSERT _131524) x s) f) ((@COND real) ((@IN _131524) x s) ((@sum _131524) s f) (real_add (f x) ((@sum _131524) s f))))))))))));
