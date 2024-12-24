require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48391 [A B C] : Prf (∀ (λ f : El (fun (prod A B) C), (∀ (λ x : El A, (∀ (λ y : El B, (= ((@CURRY A B C) f x y) (f ((@̦‚ A B) x y)))))))));
