require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51885 [A B C D] : Prf (∀ (λ f : El (fun A (fun B (fun C D))), (= ((@GABS (fun (prod A (prod B C)) D)) (λ f' : El (fun (prod A (prod B C)) D), (∀ (λ x : El A, (∀ (λ y : El B, (∀ (λ z : El C, ((@GEQ D) (f' ((@̦‚ A (prod B C)) x ((@̦‚ B C) y z))) (f x y z)))))))))) (λ t : El (prod A (prod B C)), (f ((@FST A (prod B C)) t) ((@FST B C) ((@SND A (prod B C)) t)) ((@SND B C) ((@SND A (prod B C)) t)))))));
