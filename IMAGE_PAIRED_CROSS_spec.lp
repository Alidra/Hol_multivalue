require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4360022 [A B C D] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun C D), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun C bool), (= ((@IMAGE (prod A C) (prod B D)) ((@GABS (fun (prod A C) (prod B D))) (λ f' : El (fun (prod A C) (prod B D)), (∀ (λ x : El A, (∀ (λ y : El C, ((@GEQ (prod B D)) (f' ((@̦‚ A C) x y)) ((@̦‚ B D) (f x) (g y))))))))) ((@CROSS C A) s t)) ((@CROSS D B) ((@IMAGE A B) f s) ((@IMAGE C D) g t)))))))))));
