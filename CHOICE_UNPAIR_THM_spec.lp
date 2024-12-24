require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem56945 [A B] : Prf (∀ (λ P : El (fun A (fun B bool)), (= ((@ε (prod A B)) ((@GABS (fun (prod A B) bool)) (λ f : El (fun (prod A B) bool), (∀ (λ x : El A, (∀ (λ y : El B, ((@GEQ bool) (f ((@̦‚ A B) x y)) (P x y))))))))) ((@ε (prod A B)) (λ p : El (prod A B), (P ((@FST A B) p) ((@SND A B) p)))))));
