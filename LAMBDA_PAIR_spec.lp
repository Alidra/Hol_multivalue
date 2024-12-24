require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51406 [A B C] : Prf (∀ (λ f : El (fun A (fun B C)), (= ((@GABS (fun (prod A B) C)) (λ f' : El (fun (prod A B) C), (∀ (λ x : El A, (∀ (λ y : El B, ((@GEQ C) (f' ((@̦‚ A B) x y)) (f x y)))))))) (λ p : El (prod A B), (f ((@FST A B) p) ((@SND A B) p))))));
