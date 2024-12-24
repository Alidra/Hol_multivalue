require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51711 [A B C D] : Prf (∀ (λ f : El (fun (prod A (prod B C)) D), (= (λ t : El (prod A (prod B C)), (f t)) ((@GABS (fun (prod A (prod B C)) D)) (λ f' : El (fun (prod A (prod B C)) D), (∀ (λ x : El A, (∀ (λ y : El B, (∀ (λ z : El C, ((@GEQ D) (f' ((@̦‚ A (prod B C)) x ((@̦‚ B C) y z))) (f ((@̦‚ A (prod B C)) x ((@̦‚ B C) y z)))))))))))))));
