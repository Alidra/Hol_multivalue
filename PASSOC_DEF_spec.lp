require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48787 [A B C D] : Prf (∀ (λ f : El (fun (prod (prod A B) C) D), (∀ (λ x : El A, (∀ (λ y : El B, (∀ (λ z : El C, (= ((@PASSOC A B C D) f ((@̦‚ A (prod B C)) x ((@̦‚ B C) y z))) (f ((@̦‚ (prod A B) C) ((@̦‚ A B) x y) z)))))))))));
