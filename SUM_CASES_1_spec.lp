require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7190623 [_135521] (y : El real) (f : El (fun _135521 real)) : Prf (∀ (λ s : El (fun _135521 bool), (∀ (λ a : El _135521, (⇒ (∧ ((@FINITE _135521) s) ((@IN _135521) a s)) (= ((@sum _135521) s (λ x : El _135521, ((@COND real) (= x a) y (f x)))) (real_add ((@sum _135521) s f) (real_sub y (f a)))))))));
