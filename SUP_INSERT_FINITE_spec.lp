require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5178187 : Prf (∀ (λ x : El real, (∀ (λ s : El (fun real bool), (⇒ ((@FINITE real) s) (= (sup ((@INSERT real) x s)) ((@COND real) (= s (@EMPTY real)) x (real_max x (sup s)))))))));
