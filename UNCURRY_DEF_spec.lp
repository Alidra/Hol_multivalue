require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48567 [A B C] : Prf (∀ (λ f : El (fun A (fun B C)), (∀ (λ x : El A, (∀ (λ y : El B, (= ((@UNCURRY A B C) f ((@̦‚ A B) x y)) (f x y))))))));
