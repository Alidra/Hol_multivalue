require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5256773 : Prf (∀ (λ x : El real, (∀ (λ s : El (fun real bool), (⇒ ((@FINITE real) s) (= (inf ((@INSERT real) x s)) ((@COND real) (= s (@EMPTY real)) x (real_min x (inf s)))))))));
